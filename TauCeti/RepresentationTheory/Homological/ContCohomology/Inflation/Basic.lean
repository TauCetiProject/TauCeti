/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Invariants
import TauCeti.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Inflation and the inflation-restriction sequence

Inflation is the third named instance of the compatible-pair pullback on the explicit low-degree
complex: for a normal subgroup `N` of a topological group `G` it is the pullback along the
quotient homomorphism `G → G ⧸ N` paired with the inclusion `M ^ N ↪ M` of the invariants, which
is equivariant along that homomorphism. This file defines inflation in degrees `0`, `1`, and `2`.
In degree one it proves the exactness of

```text
0 → H¹(G ⧸ N, M ^ N) → H¹(G, M) → H¹(N, M)
```

at its two nodes. In degree two, for an open normal subgroup `N` with `H¹(N, M) = 0`, it proves
the exactness of

```text
H²(G ⧸ N, M ^ N) → H²(G, M) → H²(N, M)
```

at `H²(G, M)`.

## Main definitions

* `TauCeti.ContCohomology.explicitInfl0`, `explicitInfl1`, and `explicitInfl2`: inflation on the
  explicit model in degrees `0`, `1`, and `2`.
* `TauCeti.ContCohomology.explicitInfl0Equiv`: the additive equivalence between degree-zero
  cohomology before and after inflation.
* `TauCeti.ContCohomology.descendZ1` and `descendZ2`: descent of continuous cocycles to `G ⧸ N`.

## Main statements

* `TauCeti.ContCohomology.explicitInfl0_injective` and `explicitInfl0_surjective`: inflation in
  degree zero is bijective.
* `TauCeti.ContCohomology.explicitRes1_comp_explicitInfl1` and
  `TauCeti.ContCohomology.explicitRes2_comp_explicitInfl2`: restricting an inflated class back to
  `N` gives zero.
* `TauCeti.ContCohomology.explicitInfl0_eq_explicitMap0`, `explicitInfl1_eq_explicitMap1` and
  `explicitInfl2_eq_explicitMap2`: inflation in degrees `0`, `1` and `2` is the compatible-pair
  pullback along `G → G ⧸ N`.
* `TauCeti.ContCohomology.explicitInfl1_injective`: inflation is injective in degree `1`.
* `TauCeti.ContCohomology.explicitInfRes_exact`: the image of inflation is exactly the kernel of
  restriction in degree `1`.
* `TauCeti.ContCohomology.explicitInfRes2_exact`: for an open normal subgroup `N` with
  `H¹(N, M) = 0`, the image of inflation is exactly the kernel of restriction in degree `2`.
* `TauCeti.ContCohomology.coe_descendZ1_apply_mk` and `coe_descendZ2_apply_mk`: the descents agree
  with the original cocycles on quotient representatives.
* `TauCeti.ContCohomology.explicitInfl1_descendZ1` and `explicitInfl2_descendZ2`: inflating the
  descended cocycles returns their original classes.

## Implementation notes

Inflation lives here rather than beside `explicitRes1` and `explicitCoeff1` in
`ExplicitFunctoriality.lean` because it is the one of the three named instances whose coefficients
change — it needs the invariants and their quotient action — and because the exactness statements
below are about that same map and belong with it.

The coefficients over the quotient group are Mathlib's `FixedPoints.addSubgroup N M`, with the
`G ⧸ N`-action and the coercion lemmas supplied by
`TauCeti/GroupTheory/GroupAction/FixedPoints.lean`; no second name for `M ^ N` is introduced.
Continuity of that action is carried as the instance hypothesis
`[ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]` rather than deduced from discreteness of
`M`, because nothing below uses discreteness for anything else;
`TauCeti.continuousSMulQuotientFixedPointsOfContinuousSMul` discharges it for a discrete `M`, which
is the case arising in arithmetic applications.

Everything here except `TauCeti.ContCohomology.explicitInfRes2_exact` holds for an arbitrary
topological group `G` and an arbitrary normal subgroup `N`; neither profiniteness nor closedness of
`N` is used. Closedness would only make `G ⧸ N` Hausdorff, and the descent argument in
`TauCeti.ContCohomology.explicitInfRes_exact` needs nothing but the quotient topology: a cochain
on `G` that is constant on the cosets of `N` descends to a *continuous* cochain on `G ⧸ N`
precisely because `G ⧸ N` carries that topology.

The exactness proof is the classical cochain argument. After subtracting the coboundary that
trivialises a cocycle on `N`, the corrected cocycle vanishes on `N`, hence is constant on the
cosets of `N` and takes its values in `M ^ N`, so it is the inflation of a continuous `1`-cocycle
on `G ⧸ N`. This is the continuous counterpart of Mathlib's discrete `groupCohomology.H1InfRes`
and `groupCohomology.H1InfRes_exact`, which are stated for `Rep k G` and so are unavailable at the
universe-polymorphic unbundled generality used here.

In degree two, exactness at `H²(G, M)` says that a class whose restriction to `N` vanishes is
inflated from `H²(G ⧸ N, M ^ N)`. The hypothesis `H¹(N, M) = 0` is needed: without it, the kernel
of restriction can be strictly larger than the image of inflation. The proof on cochains replaces
a cocycle killed by restriction with a cohomologous one vanishing on `G × N` and on `N × G`, which
then descends to `G ⧸ N` (`TauCeti.ContCohomology.descendZ2`). The cohomologous cocycle is built
from a choice of coset representatives of `N`; openness of `N` makes `G ⧸ N` discrete, so that
this choice, and hence the correction, is continuous.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.6.7): the
  inflation-restriction sequence, whose first three terms are the exact sequence proved here, and
  its extension to degree two when `H¹(N, M)` vanishes.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section Cosets

variable {G : Type u} [Group G] {N : Subgroup G} [N.Normal]

/-- The coset of an element of `N` is trivial. This is the form in which the cocycle computations
below evaluate an inflated cochain on `N`. -/
private theorem quotientMk_coe_eq_one (n : N) : ((n : G) : G ⧸ N) = 1 :=
  (QuotientGroup.eq_one_iff (n : G)).2 n.2

end Cosets

section CompatiblePair

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- The inclusion `M ^ N ↪ M` is equivariant along the quotient homomorphism `G → G ⧸ N`: the
`G ⧸ N`-action on an invariant element, read in `M`, is the `G`-action. This is the
compatible-pair hypothesis that inflation is the instance of `explicitMap1` and `explicitMap2`
at. -/
theorem subtype_mk'_smul (g : G) (m : FixedPoints.addSubgroup N M) :
    (FixedPoints.addSubgroup N M).subtype (QuotientGroup.mk' N g • m) =
      g • (FixedPoints.addSubgroup N M).subtype m := by
  simp only [QuotientGroup.mk'_apply, AddSubgroup.coe_subtype,
    coe_quotient_smul_fixedPoints_addSubgroup, coe_smul_fixedPoints_addSubgroup]

variable [TopologicalSpace G]

/-- The inclusion `M ^ N ↪ M` is equivariant along the continuous quotient homomorphism. -/
theorem subtype_quotientMk_smul (g : G) (m : FixedPoints.addSubgroup N M) :
    (FixedPoints.addSubgroup N M).subtype (ContinuousMonoidHom.quotientMk N g • m) =
      g • (FixedPoints.addSubgroup N M).subtype m :=
  subtype_mk'_smul G M N g m

end CompatiblePair

section DegreeZero

variable (G : Type u) [Group G]
  (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal]

/-- **Inflation in degree zero**: inclusion of the `G ⧸ N`-invariants of `M ^ N` into the
`G`-invariants of `M`. -/
def explicitInfl0 : H0 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H0 G M :=
  explicitMap0 (G ⧸ N) (FixedPoints.addSubgroup N M) (QuotientGroup.mk' N)
    (FixedPoints.addSubgroup N M).subtype (subtype_mk'_smul G M N)

/-- Degree-zero inflation does not change the underlying coefficient. -/
@[simp]
theorem coe_explicitInfl0 (m : H0 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    (explicitInfl0 G M N m : M) = (m : M) :=
  coe_explicitMap0 _ _ _ _ _ m

/-- Inflation in degree zero is the compatible-pair pullback along the quotient homomorphism
`G → G ⧸ N` and the inclusion of the invariants `M ^ N` into `M`. -/
theorem explicitInfl0_eq_explicitMap0 :
    explicitInfl0 G M N =
      explicitMap0 (G ⧸ N) (FixedPoints.addSubgroup N M) (QuotientGroup.mk' N)
        (FixedPoints.addSubgroup N M).subtype (subtype_mk'_smul G M N) := by
  rw [explicitInfl0]

/-- Degree-zero inflation is injective. In fact it is an equivalence, as packaged by
`TauCeti.ContCohomology.explicitInfl0Equiv`. -/
theorem explicitInfl0_injective : Function.Injective (explicitInfl0 G M N) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  simpa only [coe_explicitInfl0] using congrArg Subtype.val h

/-- Degree-zero inflation is surjective: a `G`-invariant element belongs to `M^N`, and remains
fixed under the quotient action. -/
theorem explicitInfl0_surjective : Function.Surjective (explicitInfl0 G M N) := by
  intro m
  have hm : ∀ g : G, g • (m : M) = m :=
    (FixedPoints.mem_addSubgroup G M (m : M)).1 m.2
  let n : FixedPoints.addSubgroup N M :=
    ⟨m, (FixedPoints.mem_addSubgroup N M (m : M)).2 fun g ↦ hm g⟩
  have hn : n ∈ H0 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
    (FixedPoints.mem_addSubgroup (G ⧸ N) (FixedPoints.addSubgroup N M) n).2 fun q ↦ by
      apply Subtype.ext
      induction q using QuotientGroup.induction_on with
      | H g => exact hm g
  refine ⟨⟨n, hn⟩, Subtype.ext ?_⟩
  exact coe_explicitInfl0 G M N ⟨n, hn⟩

/-- Inflation identifies `H⁰(G ⧸ N, M^N)` with `H⁰(G, M)`. This is the degree-zero
edge case of inflation: invariance under the quotient action is exactly invariance under `G`. -/
noncomputable def explicitInfl0Equiv :
    H0 (G ⧸ N) (FixedPoints.addSubgroup N M) ≃+ H0 G M :=
  AddEquiv.ofBijective (explicitInfl0 G M N)
    ⟨explicitInfl0_injective G M N, explicitInfl0_surjective G M N⟩

/-- The additive equivalence in degree zero has forward map `explicitInfl0`. -/
@[simp]
theorem explicitInfl0Equiv_toAddMonoidHom :
    (explicitInfl0Equiv G M N :
      H0 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H0 G M) = explicitInfl0 G M N := (rfl)

end DegreeZero

section DegreeOne

variable (G : Type u) [Group G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **Inflation in degree one**: the compatible-pair pullback along the quotient homomorphism
`G → G ⧸ N`, with the invariants `M ^ N` as coefficients. -/
noncomputable def explicitInfl1 :
    H1 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H1 G M :=
  explicitMap1 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
    (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
    (subtype_quotientMk_smul G M N)

/-- Inflation sends the class of a continuous `1`-cocycle on `G ⧸ N` to the class of the cocycle
it inflates to; `TauCeti.ContCohomology.cocyclesMap1_apply` evaluates the latter. -/
@[simp]
theorem explicitInfl1_mk (c : Z1 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    explicitInfl1 G M N (c : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (cocyclesMap1 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
        (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
        (subtype_quotientMk_smul G M N) c : H1 G M) :=
  explicitMap1_mk _ _ _ _ _ _ _ _ c

/-- Inflation in degree one is the compatible-pair pullback along the quotient homomorphism
`G → G ⧸ N` and the inclusion of the invariants `M ^ N` into `M`. -/
theorem explicitInfl1_eq_explicitMap1 :
    explicitInfl1 G M N =
      explicitMap1 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
        (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
        (subtype_quotientMk_smul G M N) := by
  rw [explicitInfl1]

/-- **Restriction to `N` kills inflation in degree one**, the first half of the
inflation-restriction sequence: the inflation of a cocycle restricts to the zero cochain on `N`,
because a continuous `1`-cocycle vanishes at `1`. -/
theorem explicitRes1_comp_explicitInfl1 :
    (explicitRes1 G M N).comp (explicitInfl1 G M N) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.comp_apply, explicitInfl1_mk, explicitRes1_mk, AddMonoidHom.zero_apply,
      H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨0, fun n => ?_⟩
    rw [cocyclesMap1_apply, cocyclesMap1_apply]
    simp [quotientMk_coe_eq_one n, map_one_of_mem_Z1 c.2]

/-- **Inflation is injective in degree one.** A cocycle on `G ⧸ N` whose inflation is the
coboundary of `m : M` has `m` fixed by `N`, so it is already the coboundary of `m` viewed in
`M ^ N`. -/
theorem explicitInfl1_injective : Function.Injective (explicitInfl1 G M N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitInfl1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    have hmem : m ∈ FixedPoints.addSubgroup N M := by
      refine (FixedPoints.mem_addSubgroup N M m).2 fun n => ?_
      have h := hm (n : G)
      rw [cocyclesMap1_apply] at h
      simp only [ContinuousMonoidHom.quotientMk_apply, quotientMk_coe_eq_one,
        map_one_of_mem_Z1 c.2, AddSubgroup.coe_subtype, ZeroMemClass.coe_zero, sub_eq_zero] at h
      exact h
    rw [H1pi_eq_zero_iff, mem_B1_iff]
    refine ⟨⟨m, hmem⟩, fun q => ?_⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      have h := hm g
      rw [cocyclesMap1_apply] at h
      refine Subtype.ext ?_
      rw [AddSubgroup.coe_sub, coe_quotient_smul_fixedPoints_addSubgroup,
        coe_smul_fixedPoints_addSubgroup]
      simpa using h

variable {G M N}

omit [ContinuousSMul G M] [N.Normal]
  [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- A continuous `1`-cocycle vanishing on `N` is constant on the cosets of `N`. -/
private theorem apply_mul_eq_self_of_vanishing {z : Z1 G M}
    (hz : ∀ n : N, (z : G → M) (n : G) = 0) (g : G) (n : N) :
    (z : G → M) (g * (n : G)) = (z : G → M) g := by
  rw [(mem_Z1_iff.1 z.2).2 g (n : G), hz n, smul_zero, zero_add]

omit [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- The values of a continuous `1`-cocycle vanishing on `N` are fixed by `N`: the cocycle identity
computes `z (n * g)` as `n • z g`, and `n * g = g * (g⁻¹ * n * g)` has its second factor in the
normal subgroup `N`. -/
private theorem smul_apply_eq_self_of_vanishing {z : Z1 G M}
    (hz : ∀ n : N, (z : G → M) (n : G) = 0) (g : G) (n : N) :
    (n : G) • (z : G → M) g = (z : G → M) g := by
  have h := (mem_Z1_iff.1 z.2).2 (n : G) g
  rw [hz n, add_zero] at h
  have hconj : ((n : G) * g) = g * (g⁻¹ * (n : G) * g) := by group
  rw [hconj, apply_mul_eq_self_of_vanishing hz g ⟨g⁻¹ * (n : G) * g,
    ‹N.Normal›.conj_mem' (n : G) n.2 g⟩] at h
  exact h.symm

/-- The descent to `G ⧸ N` of a continuous `1`-cocycle vanishing on `N`. It is well defined by
`apply_mul_eq_self_of_vanishing`, takes its values in `M ^ N` by
`smul_apply_eq_self_of_vanishing`, and is continuous because `G ⧸ N` carries the quotient
topology. Together with `TauCeti.ContCohomology.explicitInfl1_descendZ1` it says that a cocycle
vanishing on `N` is *itself* inflated, with no coboundary subtracted. -/
def descendZ1 (z : Z1 G M) (hz : ∀ n : N, (z : G → M) (n : G) = 0) :
    Z1 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  ⟨fun q => Quotient.liftOn' q
      (fun g => (⟨(z : G → M) g,
        (FixedPoints.mem_addSubgroup N M _).2 (smul_apply_eq_self_of_vanishing hz g)⟩ :
          FixedPoints.addSubgroup N M))
      fun a b hab => Subtype.ext <| by
        simpa using
          (apply_mul_eq_self_of_vanishing hz a ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.1 hab⟩).symm,
    mem_Z1_iff.2 ⟨(QuotientGroup.isQuotientMap_mk N).continuous_iff.2
        (((mem_Z1_iff.1 z.2).1).subtype_mk _), fun q q' => by
      induction q using QuotientGroup.induction_on with
      | H a =>
        induction q' using QuotientGroup.induction_on with
        | H b =>
          refine Subtype.ext ?_
          rw [AddSubgroup.coe_add, coe_quotient_smul_fixedPoints_addSubgroup,
            coe_smul_fixedPoints_addSubgroup]
          exact (mem_Z1_iff.1 z.2).2 a b⟩⟩

omit [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- The descent takes on the coset of `g` the value the original cocycle takes at `g`. This is the
computation rule that characterises `TauCeti.ContCohomology.descendZ1`. -/
@[simp]
theorem coe_descendZ1_apply_mk (z : Z1 G M) (hz : ∀ n : N, (z : G → M) (n : G) = 0)
    (g : G) :
    ((descendZ1 z hz : (G ⧸ N) → FixedPoints.addSubgroup N M) (g : G ⧸ N) : M) =
      (z : G → M) g := by
  rw [descendZ1]
  rfl

/-- Inflating the descent of a continuous `1`-cocycle vanishing on `N` returns its class. -/
theorem explicitInfl1_descendZ1 (z : Z1 G M) (hz : ∀ n : N, (z : G → M) (n : G) = 0) :
    explicitInfl1 G M N (descendZ1 z hz : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (z : H1 G M) := by
  rw [explicitInfl1_mk]
  refine congrArg (fun w : Z1 G M => (w : H1 G M)) (Subtype.ext (funext fun g => ?_))
  rw [cocyclesMap1_apply, ContinuousMonoidHom.quotientMk_apply, AddSubgroup.coe_subtype,
    coe_descendZ1_apply_mk]

variable (G M N)

/-- **Exactness of the inflation-restriction sequence at `H¹(G, M)`**: a continuous `1`-cocycle on
`G` that becomes a coboundary on `N` is, after subtracting that coboundary, inflated from
`G ⧸ N`. -/
theorem explicitInfRes_exact :
    (explicitInfl1 G M N).range = (explicitRes1 G M N).ker := by
  refine le_antisymm ((AddMonoidHom.range_le_ker_iff _ _).2
    (explicitRes1_comp_explicitInfl1 G M N)) fun x hx => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.mem_ker, explicitRes1_mk, H1pi_eq_zero_iff, mem_B1_iff] at hx
    obtain ⟨m, hm⟩ := hx
    -- Subtract the coboundary of `m`, so that the corrected cocycle `z` vanishes on `N`.
    have hmB1 : d0 G M m ∈ B1 G M := mem_B1_iff.2 ⟨m, fun g => (d0_apply m g).symm⟩
    set z : Z1 G M := c - ⟨d0 G M m, B1_le_Z1 G M hmB1⟩ with hzdef
    have hzc : (z : H1 G M) = (c : H1 G M) := by
      rw [H1pi_eq_iff, hzdef]
      simpa using neg_mem hmB1
    have hzN : ∀ n : N, (z : G → M) (n : G) = 0 := by
      intro n
      -- The `↥N`-action on `M` is the restriction of the `G`-action, so `hm n` may be read with
      -- the ambient scalar; Mathlib's `Submonoid.smul_def` is stated for a `Submonoid` and does
      -- not fire on a `Subgroup`.
      have h : (n : G) • m - m = (c : G → M) (n : G) := by
        have hn := hm n
        rw [cocyclesMap1_apply] at hn
        simp only [ContinuousMonoidHom.subgroupSubtype_apply, AddMonoidHom.id_apply] at hn
        exact hn
      simp [hzdef, ← h]
    exact ⟨(descendZ1 z hzN : H1 (G ⧸ N) (FixedPoints.addSubgroup N M)),
      (explicitInfl1_descendZ1 z hzN).trans hzc⟩

end DegreeOne

section DegreeTwo

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **Inflation in degree two.** It is not a variant of degree one: it is the last map of the
five-term exact sequence. -/
noncomputable def explicitInfl2 :
    H2 (G ⧸ N) (FixedPoints.addSubgroup N M) →+ H2 G M :=
  explicitMap2 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
    (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
    (subtype_quotientMk_smul G M N)

/-- Inflation sends the class of a continuous `2`-cocycle on `G ⧸ N` to the class of the cocycle
it inflates to; `TauCeti.ContCohomology.cocyclesMap2_apply` evaluates the latter. -/
@[simp]
theorem explicitInfl2_mk (c : Z2 (G ⧸ N) (FixedPoints.addSubgroup N M)) :
    explicitInfl2 G M N (c : H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (cocyclesMap2 (G ⧸ N) (FixedPoints.addSubgroup N M) G M (ContinuousMonoidHom.quotientMk N)
        (FixedPoints.addSubgroup N M).subtype (continuous_fixedPoints_addSubgroup_subtype G M N)
        (subtype_quotientMk_smul G M N) c : H2 G M) :=
  explicitMap2_mk _ _ _ _ _ _ _ _ c

/-- Inflation in degree two is the compatible-pair pullback along the quotient homomorphism
`G → G ⧸ N` and the inclusion of the invariants `M ^ N` into `M`. -/
theorem explicitInfl2_eq_explicitMap2 :
    explicitInfl2 G M N =
      explicitMap2 (G ⧸ N) (FixedPoints.addSubgroup N M) G M
        (ContinuousMonoidHom.quotientMk N) (FixedPoints.addSubgroup N M).subtype
        (continuous_fixedPoints_addSubgroup_subtype G M N) (subtype_quotientMk_smul G M N) := by
  rw [explicitInfl2]

/-- **Restriction to `N` kills inflation in degree two.** The inflated cocycle restricts to the
constant cochain with value `c (1, 1)`, and since `N` fixes that value the constant is the
coboundary of the constant `1`-cochain with the same value. -/
theorem explicitRes2_comp_explicitInfl2 :
    (explicitRes2 G M N).comp (explicitInfl2 G M N) = 0 := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [AddMonoidHom.comp_apply, explicitInfl2_mk, explicitRes2_mk, AddMonoidHom.zero_apply,
      H2pi_eq_zero_iff, mem_B2_iff']
    set m₀ : FixedPoints.addSubgroup N M :=
      (c : (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N M) (1, 1) with hm₀
    refine ⟨fun _ => (m₀ : M), continuous_const, fun n n' => ?_⟩
    have hfix := (FixedPoints.mem_addSubgroup N M (m₀ : M)).1 m₀.2 n
    rw [cocyclesMap2_apply, cocyclesMap2_apply]
    simp only [ContinuousMonoidHom.subgroupSubtype_apply, ContinuousMonoidHom.quotientMk_apply,
      quotientMk_coe_eq_one, AddMonoidHom.id_apply, AddSubgroup.coe_subtype, ← hm₀, hfix]
    abel

variable {G M N}

omit [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- Descend a continuous `2`-cocycle which is constant on right `N`-cosets in both variables and
whose values are fixed by `N` to a cocycle on `G ⧸ N` with values in `M ^ N`. -/
def descendZ2 (z : Z2 G M)
    (hright : ∀ (g h : G) (n n' : N),
      (z : G × G → M) (g * n, h * n') = (z : G × G → M) (g, h))
    (hfixed : ∀ (n : N) (g h : G),
      n • (z : G × G → M) (g, h) = (z : G × G → M) (g, h)) :
    Z2 (G ⧸ N) (FixedPoints.addSubgroup N M) :=
  ⟨fun q => Quotient.liftOn₂' q.1 q.2
      (fun g h => (⟨(z : G × G → M) (g, h),
        (FixedPoints.mem_addSubgroup N M _).2 fun n => hfixed n g h⟩ :
          FixedPoints.addSubgroup N M))
      fun a b a' b' ha hb => Subtype.ext <| by
        simpa using (hright a b
          ⟨a⁻¹ * a', QuotientGroup.leftRel_apply.1 ha⟩
          ⟨b⁻¹ * b', QuotientGroup.leftRel_apply.1 hb⟩).symm,
    mem_Z2_iff.2 ⟨
      ((QuotientGroup.isOpenQuotientMap_mk.prodMap
          QuotientGroup.isOpenQuotientMap_mk).isQuotientMap.continuous_iff.2 <| by
        simpa [Function.comp_def] using ((mem_Z2_iff.1 z.2).1).subtype_mk
          (fun p => (FixedPoints.mem_addSubgroup N M _).2 fun n => hfixed n p.1 p.2)),
      fun q q' q'' => by
        induction q using QuotientGroup.induction_on with
        | H g =>
          induction q' using QuotientGroup.induction_on with
          | H h =>
            induction q'' using QuotientGroup.induction_on with
            | H j =>
              refine Subtype.ext ?_
              simp only [AddSubgroup.coe_add, coe_quotient_smul_fixedPoints_addSubgroup,
                coe_smul_fixedPoints_addSubgroup, Quotient.liftOn₂'_mk'']
              exact (mem_Z2_iff.1 z.2).2 g h j⟩⟩

omit [ContinuousSMul G M] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] in
/-- The descended cocycle evaluates on quotient representatives as the original cocycle. -/
@[simp]
theorem coe_descendZ2_apply_mk (z : Z2 G M)
    (hright : ∀ (g h : G) (n n' : N),
      (z : G × G → M) (g * n, h * n') = (z : G × G → M) (g, h))
    (hfixed : ∀ (n : N) (g h : G),
      n • (z : G × G → M) (g, h) = (z : G × G → M) (g, h))
    (g h : G) :
    ((descendZ2 z hright hfixed :
      (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N M) (g, h) : M) =
      (z : G × G → M) (g, h) := by
  simp only [descendZ2, Quotient.liftOn₂'_mk'']

/-- Inflating the descent of a continuous `2`-cocycle returns the original class. -/
theorem explicitInfl2_descendZ2 (z : Z2 G M)
    (hright : ∀ (g h : G) (n n' : N),
      (z : G × G → M) (g * n, h * n') = (z : G × G → M) (g, h))
    (hfixed : ∀ (n : N) (g h : G),
      n • (z : G × G → M) (g, h) = (z : G × G → M) (g, h)) :
    explicitInfl2 G M N
        (descendZ2 z hright hfixed : H2 (G ⧸ N) (FixedPoints.addSubgroup N M)) =
      (z : H2 G M) := by
  rw [explicitInfl2_mk]
  refine congrArg (fun w : Z2 G M => (w : H2 G M)) (Subtype.ext (funext fun p => ?_))
  rw [cocyclesMap2_apply, ContinuousMonoidHom.quotientMk_apply, AddSubgroup.coe_subtype]
  -- The preceding rewrite leaves quotient representatives under the fixed-point subtype
  -- coercion; expose that evaluation so the representative computation lemma applies.
  change ((descendZ2 z hright hfixed :
    (G ⧸ N) × (G ⧸ N) → FixedPoints.addSubgroup N M) (p.1, p.2) : M) = _
  exact coe_descendZ2_apply_mk z hright hfixed p.1 p.2

end DegreeTwo

section DegreeTwoExact

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] {N : Subgroup G} [N.Normal]

/-- First step: a continuous `2`-cocycle whose restriction to `N` is the coboundary of `c` is
cohomologous to one vanishing on `G × N`. The correction is the coboundary of
`g ↦ r • c m - f (r, m) + c σ`, where `g = r m` with `r` the chosen representative of `g N` and
`m ∈ N`, and `σ` is the chosen representative of `N`. -/
private theorem exists_sub_mem_B2_vanishing_snd (hN : IsOpen (N : Set G)) (f : Z2 G M) (c : N → M)
    (hc : Continuous c)
    (hcf : ∀ n n' : N, n • c n' - c (n * n') + c n = (f : G × G → M) (n, n')) :
    ∃ f' : Z2 G M, (f : G × G → M) - f' ∈ B2 G M ∧
      ∀ (g : G) (n : N), (f' : G × G → M) (g, n) = 0 := by
  have := QuotientGroup.discreteTopology hN
  have hf := mem_Z2_iff.1 f.2
  -- The chosen representative `r g` of the coset `g N`, and the `N`-part `m g = (r g)⁻¹ g`.
  let r : G → G := fun g => (g : G ⧸ N).out
  have hr : Continuous r := continuous_of_discreteTopology.comp QuotientGroup.continuous_mk
  have hrN (g : G) : (r g)⁻¹ * g ∈ N := QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ N))
  let m : G → N := fun g => ⟨(r g)⁻¹ * g, hrN g⟩
  have hm : Continuous m := (hr.inv.mul continuous_id).subtype_mk _
  have hrm (g : G) : r g * m g = g := mul_inv_cancel_left _ _
  have hr_mul (g : G) (n : N) : r (g * n) = r g := by
    simp only [r, QuotientGroup.mk_mul_of_mem g n.2]
  have hm_mul (g : G) (n : N) : m (g * n) = m g * n :=
    Subtype.ext (by simp only [m, hr_mul, Subgroup.coe_mul, mul_assoc])
  let σ : N := ⟨r 1, by simpa using hrN 1⟩
  have hr_N (n : N) : r n = σ := by
    simp only [r, σ, (QuotientGroup.eq_one_iff _).2 n.2, QuotientGroup.mk_one]
  have hm_N (n : N) : m n = σ⁻¹ * n := Subtype.ext (by simp only [m, hr_N, Subgroup.coe_mul,
    Subgroup.coe_inv])
  let b : G → M := fun g => r g • c (m g) - (f : G × G → M) (r g, m g) + c σ
  have hb : Continuous b :=
    ((hr.smul (hc.comp hm)).sub (hf.1.comp (hr.prodMk (continuous_subtype_val.comp hm)))).add
      continuous_const
  -- On `N` the correction `b` is `c`.
  have hbN (n : N) : b n = c n := by
    have h := hcf σ (σ⁻¹ * n)
    simp only [b, hr_N, hm_N, mul_inv_cancel_left, Subgroup.smul_def] at h ⊢
    rw [← h]
    abel
  -- On `G × N` the coboundary of `b` is `f`, by the cocycle identity of `f` at `(r g, m g, n)`
  -- and the coboundary identity of `c` at `(m g, n)`.
  have hd (g : G) (n : N) : d1 G M b (g, n) = (f : G × G → M) (g, n) := by
    have h₁ := hf.2 (r g) (m g) n
    have h₂ := congrArg (r g • ·) (hcf (m g) n)
    simp only [Subgroup.smul_def, smul_add, smul_sub, smul_smul, hrm] at h₁ h₂
    rw [d1_apply, hbN]
    simp only [b, hr_mul, hm_mul, Subgroup.coe_mul]
    linear_combination (norm := abel) h₂ - h₁
  refine ⟨f - ⟨d1 G M b, B2_le_Z2 G M (mem_B2_iff.2 ⟨b, hb, rfl⟩)⟩, ?_, fun g n => ?_⟩
  · simpa using mem_B2_iff.2 ⟨b, hb, rfl⟩
  · simp [hd]

/-- Second step: when `H¹(N, M)` vanishes, a continuous `2`-cocycle vanishing on `G × N` is
cohomologous to one vanishing on `G × N` and on `N × G`. -/
private theorem exists_sub_mem_B2_vanishing (hN : IsOpen (N : Set G)) [Subsingleton (H1 N M)]
    (f : Z2 G M) (hR : ∀ (g : G) (n : N), (f : G × G → M) (g, n) = 0) :
    ∃ f' : Z2 G M, (f : G × G → M) - f' ∈ B2 G M ∧
      (∀ (g : G) (n : N), (f' : G × G → M) (g, n) = 0) ∧
        ∀ (n : N) (g : G), (f' : G × G → M) (n, g) = 0 := by
  have := QuotientGroup.discreteTopology hN
  have hf := mem_Z2_iff.1 f.2
  -- For each `h`, the function `n ↦ f (n, h)` is a continuous `1`-cocycle on `N`, hence a
  -- coboundary `n ↦ n • x h - x h`.
  have hx (h : G) : ∃ x : M, ∀ n : N, n • x - x = (f : G × G → M) (n, h) := by
    let φ : Z1 N M := ⟨fun n => (f : G × G → M) (n, h), mem_Z1_iff.2
      ⟨hf.1.comp (continuous_subtype_val.prodMk continuous_const), fun n n' => by
        have h₁ := hf.2 n n' h
        -- `n' * h = h * (h⁻¹ * n' * h)`, with `h⁻¹ * n' * h ∈ N` by normality.
        have h₂ := groupCohomology.apply_mul_snd_of_isCocycle₂_of_vanishing hf.2 hR n h
          ⟨_, ‹N.Normal›.conj_mem' _ n'.2 h⟩
        rw [← mul_assoc, mul_inv_cancel_left] at h₂
        rw [hR, add_zero, h₂] at h₁
        exact h₁⟩⟩
    have h0 : (φ : H1 N M) = 0 := Subsingleton.elim _ _
    exact mem_B1_iff.1 (H1pi_eq_zero_iff.1 h0)
  choose x hx using hx
  let e : G → M := fun g => x (g : G ⧸ N).out - x (1 : G ⧸ N).out
  have he : Continuous e :=
    (continuous_of_discreteTopology (f := fun q : G ⧸ N => x q.out - x (1 : G ⧸ N).out)).comp
      QuotientGroup.continuous_mk
  have he_mul (g : G) (n : N) : e (g * n) = e g := by
    simp only [e, QuotientGroup.mk_mul_of_mem g n.2]
  have he_N (n : N) : e n = 0 := by
    simp only [e, (QuotientGroup.eq_one_iff _).2 n.2, sub_self]
  have hσ : ((1 : G ⧸ N).out : G) ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.out_eq']
  have hs (g : G) : ((g : G ⧸ N).out)⁻¹ * g ∈ N :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (g : G ⧸ N))
  refine ⟨f - ⟨d1 G M e, B2_le_Z2 G M (mem_B2_iff.2 ⟨e, he, rfl⟩)⟩, ?_, fun g n => ?_,
    fun n g => ?_⟩
  · simpa using mem_B2_iff.2 ⟨e, he, rfl⟩
  · simp [hR, he_mul, he_N]
  · -- `n • e g - e g` is `f (n, r) - f (n, σ) = f (n, g)`, for the representatives `r` of `g N`
    -- and `σ` of `N`.
    have hng : e (n * g) = e g := by
      simp only [e, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 n.2, one_mul]
    have h₁ := hx (g : G ⧸ N).out n
    have h₂ := hx (1 : G ⧸ N).out n
    rw [hR n ⟨_, hσ⟩] at h₂
    rw [← groupCohomology.apply_mul_snd_of_isCocycle₂_of_vanishing hf.2 hR n _ ⟨_, hs g⟩,
      mul_inv_cancel_left] at h₁
    simp only [AddSubgroup.coe_sub, Pi.sub_apply, d1_apply, hng, he_N, e, smul_sub]
    rw [Subgroup.smul_def] at h₁ h₂
    linear_combination (norm := abel) h₂ - h₁

variable (G M N) in
/-- **Exactness of the inflation-restriction sequence at `H²(G, M)`** when `H¹(N, M)` vanishes,
for an open normal subgroup `N`: a class of `H²(G, M)` whose restriction to `N` vanishes is
inflated from `H²(G ⧸ N, M ^ N)`. -/
theorem explicitInfRes2_exact (hN : IsOpen (N : Set G))
    [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)] [Subsingleton (H1 N M)] :
    (explicitInfl2 G M N).range = (explicitRes2 G M N).ker := by
  refine le_antisymm ((AddMonoidHom.range_le_ker_iff _ _).2
    (explicitRes2_comp_explicitInfl2 G M N)) fun x hx => ?_
  induction x using QuotientAddGroup.induction_on with
  | _ f =>
    rw [AddMonoidHom.mem_ker, explicitRes2_mk, H2pi_eq_zero_iff, mem_B2_iff'] at hx
    obtain ⟨c, hc, hcf⟩ := hx
    obtain ⟨f₁, hf₁, hR₁⟩ := exists_sub_mem_B2_vanishing_snd hN f c hc fun n n' => by
      simpa [cocyclesMap2_apply] using hcf n n'
    obtain ⟨f₂, hf₂, hR, hL⟩ := exists_sub_mem_B2_vanishing hN f₁ hR₁
    have hf := (mem_Z2_iff.1 f₂.2).2
    have hff₂ : (f : H2 G M) = f₂ := H2pi_eq_iff.2 (by simpa using add_mem hf₁ hf₂)
    refine ⟨descendZ2 f₂ (fun g h n n' => ?_)
      (groupCohomology.smul_apply_of_isCocycle₂_of_vanishing hf hR hL),
      (explicitInfl2_descendZ2 _ _ _).trans hff₂.symm⟩
    rw [groupCohomology.apply_mul_snd_of_isCocycle₂_of_vanishing hf hR,
      groupCohomology.apply_mul_fst_of_isCocycle₂_of_vanishing hf hR hL]

end DegreeTwoExact

end TauCeti.ContCohomology
