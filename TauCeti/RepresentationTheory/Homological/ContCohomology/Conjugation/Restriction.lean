/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Conjugation.Basic
import TauCeti.Topology.Algebra.ConstMulAction

/-!
# Restriction and conjugation in explicit continuous cohomology

For subgroups `U, V ≤ G` and `g : G`, let `κ : V → U` have underlying function
`v ↦ g⁻¹ * v * g`. The compatible pair of `κ` and the coefficient action of `g` carries
restriction to `U` to restriction to `V`, in degrees zero, one and two. In particular,
restriction to conjugate subgroups agrees after identifying their cohomology by conjugation.
Neither subgroup has to be normal, closed, open or of finite index; even an inclusion
`V ≤ gUg⁻¹` suffices.

The positive-degree identities hold on classes, not on cochains. In degree one the correction
is `d⁰(c g)`. In degree two it is `d¹ b`, where
`b v = c (g, g⁻¹ * v * g) - c (v, g)` is the restriction of
`inverseConjugationHomotopy2 g c`. Its continuity is essential: the explicit quotient divides
only by differentials of continuous cochains. The named cochain identity
`cochainsMap2_res_sub_eq_d1_of_conj` makes this correction available for computations.

These are the restriction identities for the conjugation maps of Neukirch, Schmidt and
Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I, §5. The homotopy follows the
existing `inverseConjugationCochainHomotopy2_of_isCocycle` construction; inner conjugation
acts trivially as in Milne, *Arithmetic Duality Theorems*, Proposition 0.15.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM

section DegreeZero

variable (G : Type uG) [Group G] (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (U V : Subgroup G) (g : G) (κ : V →* U)
  (hκ : ∀ v : V, (κ v : G) = g⁻¹ * v * g)
  (f : M →+ M) (hf : ∀ m : M, f m = g • m)

include hκ hf in
/-- Inverse conjugation on subgroups is compatible with the conjugating action on coefficients. -/
theorem inverseConjugation_smul_of_eq (v : V) (m : M) :
    f (κ v • m) = v • f m := by
  simp [hf, Subgroup.smul_def, hκ, smul_smul, mul_assoc]

/-- Conjugation carries restriction to `U` to restriction to `V` in degree zero.
The group map may identify `V` with any subgroup of `gUg⁻¹`. -/
-- Not `@[simp]`: the conjugating element occurs only in the hypotheses on `κ` and `f`.
theorem explicitMap0_explicitRes0_of_conj (x : H0 G M) :
    explicitMap0 U M κ f
      (inverseConjugation_smul_of_eq G M U V g κ hκ f hf)
      (explicitRes0 G M U x) = explicitRes0 G M V x := by
  apply Subtype.ext
  simp only [coe_explicitMap0, coe_explicitRes0, hf]
  exact (FixedPoints.mem_addSubgroup G M (x : M)).1 x.property g

end DegreeZero

section PositiveDegrees

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (U V : Subgroup G) (g : G) (κ : V →ₜ* U)
  (hκ : ∀ v : V, (κ v : G) = g⁻¹ * v * g)
  (f : M →+ M) (hf : ∀ m : M, f m = g • m)

omit [IsTopologicalGroup G] [ContinuousSMul G M] in
/-- Conjugating the restriction of a continuous `1`-cocycle changes it by the coboundary of its
value at the conjugating element. This is the representative-level restriction identity. -/
theorem smul_inverseConjugation_apply_sub_eq_d0 (c : Z1 G M) (g : G) (v : V) :
    g • (c : G → M) (g⁻¹ * (v : G) * g) - (c : G → M) (v : G) =
      d0 V M ((c : G → M) g) v := by
  rw [groupCohomology.smul_apply_inv_mul_mul_of_isCocycle₁ (mem_Z1_iff.1 c.2).2 g (v : G),
    d0_apply, Subgroup.smul_def]
  abel

omit [IsTopologicalGroup G] in
/-- Conjugation carries restriction to `U` to restriction to `V` in degree one.
The equality is on classes; on cocycles the correction is `d⁰(c g)`. -/
theorem explicitMap1_explicitRes1_of_conj (x : H1 G M) :
    explicitMap1 U M V M κ f (by exact continuous_of_eq_smul g hf)
      (inverseConjugation_smul_of_eq G M U V g κ hκ f hf)
      (explicitRes1 G M U x) = explicitRes1 G M V x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitRes1_mk, explicitMap1_mk, explicitRes1_mk, H1pi_eq_iff]
    refine mem_B1_iff.2 ⟨(c : G → M) g, fun v => ?_⟩
    simp only [Pi.sub_apply, cocyclesMap1_apply, AddMonoidHom.id_apply,
      ContinuousMonoidHom.subgroupSubtype_apply, hf, hκ]
    simpa only [d0_apply] using
      (smul_inverseConjugation_apply_sub_eq_d0 G M V c g v).symm

include hκ hf in
omit [ContinuousSMul G M] [IsTopologicalGroup G] in
/-- The degree-two conjugation correction on restricted cocycles is the differential of the
restricted bar homotopy. This is an equality of cochains, before taking classes. -/
theorem cochainsMap2_res_sub_eq_d1_of_conj (c : Z2 G M) :
    cochainsMap2 (κ : V →* U) f (fun p : U × U => (c : G × G → M) (p.1, p.2)) -
        (fun p : V × V => (c : G × G → M) (p.1, p.2)) =
      d1 V M (fun v : V => inverseConjugationHomotopy2 g c v) := by
  funext ⟨v, w⟩
  have h := congrFun
    (inverseConjugationCochainHomotopy2_of_isCocycle g (c : G × G → M)
      (mem_Z2_iff.1 c.property).2) ((v : G), (w : G))
  simpa [cochainsMap2_apply, hf, hκ, MulAut.conj_apply,
    d1_apply, Subgroup.smul_def] using h

omit [IsTopologicalGroup G] in
variable [ContinuousMul G] [ContinuousMul U] [ContinuousMul V] in
/-- Conjugation carries restriction to `U` to restriction to `V` in degree two.
The cochain correction is the differential of a continuous restricted bar homotopy. -/
theorem explicitMap2_explicitRes2_of_conj (x : H2 G M) :
    explicitMap2 U M V M κ f (by exact continuous_of_eq_smul g hf)
      (inverseConjugation_smul_of_eq G M U V g κ hκ f hf)
      (explicitRes2 G M U x) = explicitRes2 G M V x := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitRes2_mk, explicitMap2_mk, explicitRes2_mk, H2pi_eq_iff]
    refine mem_B2_iff.2 ⟨fun v : V => inverseConjugationHomotopy2 g c v,
      (continuous_inverseConjugationHomotopy2 g (mem_Z2_iff.1 c.property).1).comp
        continuous_subtype_val, ?_⟩
    funext ⟨v, w⟩
    simpa [cocyclesMap2_apply, cochainsMap2_apply] using
      congrFun (cochainsMap2_res_sub_eq_d1_of_conj G M U V g κ hκ f hf c).symm (v, w)

end PositiveDegrees

end TauCeti.ContCohomology
