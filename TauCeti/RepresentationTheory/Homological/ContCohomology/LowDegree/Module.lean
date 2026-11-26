/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality

/-!
# Scalar actions on the explicit `H¹` and `H²`

The explicit groups `H¹(G, M) = Z¹/B¹` and `H²(G, M) = Z²/B²` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree` are defined for a bare
topological abelian group `M` with a continuous action of `G`; no coefficient ring enters the
definition. When `M` is moreover a module over a semiring `R`, the action of `G` commutes with
that of `R` and each scalar acts continuously, the scalar `r` acts on `H¹(G, M)` and `H²(G, M)`
through the coefficient map of the equivariant endomorphism `r • ·` of `M`, that is, by
`r • [z] = [r • z]` on the class of a cocycle `z`. This file installs these actions as instances,
so that the explicit groups, not a copy of them, carry the `R`-module structure.

## Main definitions

* `TauCeti.ContCohomology.H1.smulRingHom` and `TauCeti.ContCohomology.H2.smulRingHom`: the
  scalar `r` acting by the coefficient map `explicitMap1`/`explicitMap2` of `r • ·`, as a ring
  homomorphism into the additive endomorphisms.
* `TauCeti.ContCohomology.H1.instModule` and `TauCeti.ContCohomology.H2.instModule`: `H¹(G, M)`
  and `H²(G, M)` are `R`-modules.

## Main results

* `TauCeti.ContCohomology.H1.smul_def` and `TauCeti.ContCohomology.H2.smul_def`: a scalar acts
  as the coefficient map of `r • ·`.
* `TauCeti.ContCohomology.H1.smul_mk` and `TauCeti.ContCohomology.H2.smul_mk`: a scalar acts on
  the class of a cocycle as on the cocycle.
* `TauCeti.ContCohomology.smul_mem_Z1`, `smul_mem_B1`, `smul_mem_Z2`, `smul_mem_B2`: cocycles and
  coboundaries are stable under the scalars. They are proved from the cocycle and coboundary
  identities, so that, like `B1`, `Z1`, `Z2` and `B2` themselves, they need no multiplication on
  `G` in degree `0` and only a multiplication in the higher degrees; the coefficient-map lemmas
  `cochainsMap1_mem_Z1`, `cochainsMap1_mem_B1`, `cochainsMap2_mem_Z2` and `cochainsMap2_mem_B2`
  would give them only for a monoid `G`.

## Implementation notes

The scalar `r` acts through the existing functoriality `explicitMap1`/`explicitMap2` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality`, applied to the
identity of `G` and the equivariant coefficient map `r • ·`, and the module structure is
`Module.compHom` of the resulting ring homomorphism. The instances in the case `R = ZMod n` are
found through `TauCeti.ZMod.smulCommClass'` and `TauCeti.ZMod.continuousConstSMul`.

At `R = ℤ` the instances differ from the `ℤ`-module structure `AddCommGroup.toIntModule` that
every abelian group carries: the two agree only propositionally, by Mathlib's `int_smul_eq_zsmul`
or `AddCommGroup.uniqueIntModule`. The instances therefore have low priority, so that
`Module ℤ (H1 G M)` and `ℤ`-scalar multiplication keep resolving to the structure of the abelian
group.

## References

The design, in which the cohomology is defined once for abelian groups and the `R`-module
structure is supplied by instances where it exists, follows David Loeffler's advice in
[#Riemann-Hypothesis > Library design discrepancies between RH/Mathlib/TauCeti](https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780293).
It builds on the explicit groups of the existing Tau Ceti file
`TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree`.
-/

public section

namespace TauCeti.ContCohomology

universe u v w

/-! ### Stability of cocycles and coboundaries -/

section Stability

variable {R : Type w} {G : Type u} {M : Type v} [AddCommGroup M] [DistribSMul R M]

/-- Pulling a `1`-cochain back along the identity of `G` and the coefficient map `r • ·` is
multiplication by `r`. -/
theorem cochainsMap1_smul [Monoid G] (r : R) (f : G → M) :
    cochainsMap1 (MonoidHom.id G) (DistribSMul.toAddMonoidHom M r) f = r • f :=
  funext fun g ↦ cochainsMap1_apply _ _ f g

/-- Pulling a `2`-cochain back along the identity of `G` and the coefficient map `r • ·` is
multiplication by `r`. -/
theorem cochainsMap2_smul [Monoid G] (r : R) (f : G × G → M) :
    cochainsMap2 (MonoidHom.id G) (DistribSMul.toAddMonoidHom M r) f = r • f :=
  funext fun ⟨g, h⟩ ↦ cochainsMap2_apply _ _ f g h

variable [DistribSMul G M] [SMulCommClass G R M]

/-- The `1`-coboundaries are stable under the scalars. -/
theorem smul_mem_B1 (r : R) {f : G → M} (hf : f ∈ B1 G M) : r • f ∈ B1 G M := by
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hf
  refine mem_B1_iff.2 ⟨r • m, fun g ↦ ?_⟩
  rw [Pi.smul_apply, ← hm g, smul_sub, smul_comm g r m]

variable [Mul G] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]

/-- The continuous `1`-cocycles are stable under continuous scalars. -/
theorem smul_mem_Z1 (r : R) {f : G → M} (hf : f ∈ Z1 G M) : r • f ∈ Z1 G M := by
  obtain ⟨hc, hf⟩ := mem_Z1_iff.1 hf
  refine mem_Z1_iff.2 ⟨hc.const_smul r, fun g h ↦ ?_⟩
  simp only [Pi.smul_apply, hf g h, smul_add, smul_comm g r]

/-- The continuous `2`-cocycles are stable under continuous scalars. -/
theorem smul_mem_Z2 (r : R) {f : G × G → M} (hf : f ∈ Z2 G M) : r • f ∈ Z2 G M := by
  obtain ⟨hc, hf⟩ := mem_Z2_iff.1 hf
  refine mem_Z2_iff.2 ⟨hc.const_smul r, fun g h j ↦ ?_⟩
  simp only [Pi.smul_apply, ← smul_add, hf g h j, smul_comm g r]

/-- The `2`-coboundaries are stable under continuous scalars. -/
theorem smul_mem_B2 (r : R) {f : G × G → M} (hf : f ∈ B2 G M) : r • f ∈ B2 G M := by
  obtain ⟨c, hc, rfl⟩ := mem_B2_iff.1 hf
  refine mem_B2_iff.2 ⟨r • c, hc.const_smul r, funext fun ⟨g, h⟩ ↦ ?_⟩
  simp only [d1_apply, Pi.smul_apply, smul_comm g r, smul_add, smul_sub]

end Stability

/-! ### The module structures -/

section Instances

variable {R : Type w} [Semiring R] {G : Type u} [Monoid G] [TopologicalSpace G]
  {M : Type v} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [SMulCommClass G R M] [ContinuousConstSMul R M]

variable (R G M) in
/-- The action of the scalars on `H¹(G, M)`: the scalar `r` acts by the coefficient map
`explicitMap1` of the equivariant map `r • ·`, as a ring homomorphism into the additive
endomorphisms. -/
def H1.smulRingHom : R →+* AddMonoid.End (H1 G M) where
  toFun r := explicitMap1 G M G M (ContinuousMonoidHom.id G) (DistribSMul.toAddMonoidHom M r)
    (continuous_const_smul r) fun g m ↦ (smul_comm g r m).symm
  map_one' := (explicitMap1_congr_of_eq G M G M _ _ _ (AddMonoidHom.id M) (hq := continuous_id)
    (hψ := fun _ _ ↦ rfl) rfl (AddMonoidHom.ext (one_smul R))).trans (explicitMap1_id G M)
  map_mul' r s := (explicitMap1_congr_of_eq G M G M _
    ((ContinuousMonoidHom.id G).comp (ContinuousMonoidHom.id G)) _
    ((DistribSMul.toAddMonoidHom M r).comp (DistribSMul.toAddMonoidHom M s))
    (ContinuousMonoidHom.ext fun _ ↦ rfl) (AddMonoidHom.ext (mul_smul r s))).trans
    (explicitMap1_comp G M G M _ _
      (continuous_const_smul s) (fun g m ↦ (smul_comm g s m).symm) G M _ _
      (continuous_const_smul r) (fun g m ↦ (smul_comm g r m).symm))
  -- `r • ·` as an equivariant map of `M`, which needs the scalars on the left; `toFun r` is its
  -- coefficient map `explicitCoeff1`, by `explicitCoeff1_eq_explicitMap1`
  map_zero' := by
    have := SMulCommClass.symm G R M
    exact (explicitCoeff1_eq_explicitMap1 G M (SMulCommClass.toDistribMulActionHom G M (0 : R))
      (continuous_const_smul 0)).symm.trans (explicitCoeff1_eq_zero G M _ _ (zero_smul R))
  map_add' r s := by
    have := SMulCommClass.symm G R M
    let f (t : R) : M →+[G] M := SMulCommClass.toDistribMulActionHom G M t
    have hf (t : R) : Continuous (f t) := continuous_const_smul t
    exact (explicitCoeff1_eq_explicitMap1 G M (f (r + s)) (hf (r + s))).symm.trans
      ((explicitCoeff1_eq_add G M (f r) (f s) (f (r + s)) (hf r) (hf s) (hf (r + s))
        (add_smul r s)).trans (congrArg₂ (· + ·) (explicitCoeff1_eq_explicitMap1 G M (f r) (hf r))
          (explicitCoeff1_eq_explicitMap1 G M (f s) (hf s))))

/-- **`H¹(G, M)` is an `R`-module** when `M` is one, with continuous scalars commuting with the
action of `G`: `r` acts by the coefficient map of `r • ·`. -/
instance (priority := 100) H1.instModule : Module R (H1 G M) :=
  Module.compHom _ (H1.smulRingHom R G M)

/-- A scalar acts on `H¹(G, M)` as the coefficient map of `r • ·`. -/
theorem H1.smul_def (r : R) (x : H1 G M) :
    r • x = explicitMap1 G M G M (ContinuousMonoidHom.id G) (DistribSMul.toAddMonoidHom M r)
      (continuous_const_smul r) (fun g m ↦ (smul_comm g r m).symm) x :=
  (rfl)

/-- A scalar acts on the class of a `1`-cocycle as on the cocycle. -/
@[simp]
theorem H1.smul_mk (r : R) (z : Z1 G M) :
    r • (z : H1 G M) = ((⟨r • (z : G → M), smul_mem_Z1 r z.property⟩ : Z1 G M) : H1 G M) :=
  (explicitMap1_mk G M G M _ _ _ _ z).trans
    (congrArg _ (Subtype.ext ((coe_cocyclesMap1 G M G M _ _ _ _ z).trans
      (cochainsMap1_smul r (z : G → M)))))

variable [ContinuousMul G]

variable (R G M) in
/-- The action of the scalars on `H²(G, M)`: the scalar `r` acts by the coefficient map
`explicitMap2` of the equivariant map `r • ·`, as a ring homomorphism into the additive
endomorphisms. -/
def H2.smulRingHom : R →+* AddMonoid.End (H2 G M) where
  toFun r := explicitMap2 G M G M (ContinuousMonoidHom.id G) (DistribSMul.toAddMonoidHom M r)
    (continuous_const_smul r) fun g m ↦ (smul_comm g r m).symm
  map_one' := (explicitMap2_congr_of_eq G M G M _ _ _ (AddMonoidHom.id M) (hq := continuous_id)
    (hψ := fun _ _ ↦ rfl) rfl (AddMonoidHom.ext (one_smul R))).trans (explicitMap2_id G M)
  map_mul' r s := (explicitMap2_congr_of_eq G M G M _
    ((ContinuousMonoidHom.id G).comp (ContinuousMonoidHom.id G)) _
    ((DistribSMul.toAddMonoidHom M r).comp (DistribSMul.toAddMonoidHom M s))
    (ContinuousMonoidHom.ext fun _ ↦ rfl) (AddMonoidHom.ext (mul_smul r s))).trans
    (explicitMap2_comp G M G M _ _
      (continuous_const_smul s) (fun g m ↦ (smul_comm g s m).symm) G M _ _
      (continuous_const_smul r) (fun g m ↦ (smul_comm g r m).symm))
  map_zero' := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun z ↦ ?_)
    refine (explicitMap2_mk G M G M _ _ _ _ z).trans ?_
    refine (congrArg _ (Subtype.ext (funext fun ⟨g, h⟩ ↦ ?_))).trans (QuotientAddGroup.mk_zero _)
    exact (cocyclesMap2_apply G M G M _ _ _ _ z g h).trans (zero_smul R _)
  map_add' r s := by
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun z ↦ ?_)
    refine (explicitMap2_mk G M G M _ _ _ _ z).trans (.trans ?_ (congrArg₂ (· + ·)
      (explicitMap2_mk G M G M _ (DistribSMul.toAddMonoidHom M r) _ _ z).symm
      (explicitMap2_mk G M G M _ (DistribSMul.toAddMonoidHom M s) _ _ z).symm))
    refine (congrArg _ (Subtype.ext (funext fun ⟨g, h⟩ ↦ ?_))).trans (QuotientAddGroup.mk_add _ _ _)
    exact (cocyclesMap2_apply G M G M _ _ _ _ z g h).trans ((add_smul r s _).trans
      (congrArg₂ (· + ·)
        (cocyclesMap2_apply G M G M _ (DistribSMul.toAddMonoidHom M r) _ _ z g h).symm
        (cocyclesMap2_apply G M G M _ (DistribSMul.toAddMonoidHom M s) _ _ z g h).symm))

/-- **`H²(G, M)` is an `R`-module** when `M` is one, with continuous scalars commuting with the
action of `G`: `r` acts by the coefficient map of `r • ·`. -/
instance (priority := 100) H2.instModule : Module R (H2 G M) :=
  Module.compHom _ (H2.smulRingHom R G M)

/-- A scalar acts on `H²(G, M)` as the coefficient map of `r • ·`. -/
theorem H2.smul_def (r : R) (x : H2 G M) :
    r • x = explicitMap2 G M G M (ContinuousMonoidHom.id G) (DistribSMul.toAddMonoidHom M r)
      (continuous_const_smul r) (fun g m ↦ (smul_comm g r m).symm) x :=
  (rfl)

/-- A scalar acts on the class of a `2`-cocycle as on the cocycle. -/
@[simp]
theorem H2.smul_mk (r : R) (z : Z2 G M) :
    r • (z : H2 G M) = ((⟨r • (z : G × G → M), smul_mem_Z2 r z.property⟩ : Z2 G M) : H2 G M) :=
  (explicitMap2_mk G M G M _ _ _ _ z).trans
    (congrArg _ (Subtype.ext ((coe_cocyclesMap2 G M G M _ _ _ _ z).trans
      (cochainsMap2_smul r (z : G × G → M)))))

end Instances

end TauCeti.ContCohomology
