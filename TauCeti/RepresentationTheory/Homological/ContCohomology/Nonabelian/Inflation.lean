/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.OfQuotient
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic
import TauCeti.GroupTheory.GroupAction.FixedPoints

/-!
# Inflation in continuous nonabelian first cohomology

Let `N` be a normal subgroup of a topological group `G` acting on a topological group `A`. The
quotient `G ⧸ N`, with the quotient topology, acts on the fixed points `Aᴺ`, and **inflation**

`H¹(G ⧸ N, Aᴺ) → H¹(G, A)`

is the map induced by the compatible pair formed by the projection `G → G ⧸ N` and the inclusion
`Aᴺ ↪ A`. This file proves the nonabelian inflation–restriction sequence

`1 → H¹(G ⧸ N, Aᴺ) → H¹(G, A) → H¹(N, A)`,

an exact sequence of pointed sets: inflation is injective, and a class restricts to the base
point of `H¹(N, A)` exactly when it is inflated.

For `G` compact and `A` discrete this gives the reduction of `H¹(G, A)` to finite quotients:
every class is inflated from `G ⧸ U` for an open normal subgroup `U`, and `G ⧸ U` is finite.
Together with the injectivity of inflation, `H¹(G, A)` is the union of the injective images of
the sets `H¹(G ⧸ U, Aᵁ)`. For a profinite Galois group this is the reduction of continuous Galois
cohomology to the cohomology of finite Galois extensions.

The key construction is `TauCeti.NonabelianH1.Cocycle.descend`: a cocycle trivial on `N` is
constant on the cosets of `N`, takes values in `Aᴺ`, and so descends to a cocycle of `G ⧸ N`.

## Main definitions

* `TauCeti.NonabelianH1.infl`: inflation `H¹(G ⧸ N, Aᴺ) → H¹(G, A)`.
* `TauCeti.NonabelianH1.Cocycle.descend`: the cocycle of `G ⧸ N` with values in `Aᴺ` induced by a
  cocycle trivial on `N`.

## Main results

* `TauCeti.NonabelianH1.infl_injective`: inflation is injective.
* `TauCeti.NonabelianH1.res_eq_one_iff`: a class restricts to the base point exactly when it is
  inflated.
* `TauCeti.NonabelianH1.exists_mem_range_infl`: for `G` compact and `A` discrete, every class is
  inflated from the quotient by an open normal subgroup.

## References

* J.-P. Serre, *Galois Cohomology*, Springer, 1997, I.2.2 and I.5.8.
-/

public section

namespace TauCeti

namespace NonabelianH1

variable {G A : Type*} [Group G] [TopologicalSpace G] [Group A] [TopologicalSpace A]
  [MulDistribMulAction G A]

variable (N : Subgroup G) [N.Normal]

/-- The projection `G → G ⧸ N` and the inclusion `Aᴺ ↪ A` form a compatible pair. -/
theorem subgroupSubtype_quotientMk_smul (g : G) (a : FixedPoints.subgroup N A) :
    ContinuousMonoidHom.subgroupSubtype _ (Subgroup.quotientMkContinuousMonoidHom N g • a) =
      g • ContinuousMonoidHom.subgroupSubtype _ a :=
  coe_quotient_smul_fixedPoints_subgroup g a

/-- **Inflation** `H¹(G ⧸ N, Aᴺ) → H¹(G, A)`: the map induced by the projection `G → G ⧸ N` and the
inclusion of the fixed points `Aᴺ ↪ A`. -/
def infl : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A) → NonabelianH1 G A :=
  map (Subgroup.quotientMkContinuousMonoidHom N) (ContinuousMonoidHom.subgroupSubtype _)
    (subgroupSubtype_quotientMk_smul N)

/-- Inflation composes a representing cocycle with the projection `G → G ⧸ N`. -/
theorem infl_mk (f : Cocycle (G ⧸ N) (FixedPoints.subgroup N A)) :
    infl N (mk f) =
      mk (f.map (Subgroup.quotientMkContinuousMonoidHom N) (ContinuousMonoidHom.subgroupSubtype _)
        (subgroupSubtype_quotientMk_smul N)) :=
  map_mk _ _ _ f

/-- Inflation preserves the base point. -/
@[simp]
theorem infl_one : infl N (1 : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)) = 1 :=
  map_one _ _ _

namespace Cocycle

variable {N} {f : Cocycle G A}

omit [N.Normal] in
/-- A cocycle trivial on `N` is constant on the cosets `g * N`. -/
theorem apply_mul_of_mem (hf : ∀ n ∈ N, f n = 1) (g : G) {n : G} (hn : n ∈ N) :
    f (g * n) = f g := by
  rw [f.apply_mul, hf n hn, smul_one, mul_one]

/-- A cocycle trivial on `N` takes values fixed by `N`. -/
theorem smul_apply_of_mem (hf : ∀ n ∈ N, f n = 1) (g : G) {n : G} (hn : n ∈ N) :
    n • f g = f g := by
  have hconj : g⁻¹ * n * g ∈ N := by
    simpa using ‹N.Normal›.conj_mem n hn g⁻¹
  calc n • f g = f (n * g) := by rw [f.apply_mul, hf n hn, one_mul]
    _ = f (g * (g⁻¹ * n * g)) := by group
    _ = f g := apply_mul_of_mem hf g hconj

variable (N)

/-- The cocycle of `G ⧸ N` with values in `Aᴺ` induced by a cocycle `f` of `G` trivial on `N`:
`f` is constant on the cosets of `N` and takes values in `Aᴺ`. -/
def descend (f : Cocycle G A) (hf : ∀ n ∈ N, f n = 1) :
    Cocycle (G ⧸ N) (FixedPoints.subgroup N A) where
  toFun q := Quotient.liftOn' q
    (fun g ↦ (⟨f g, fun n ↦ smul_apply_of_mem hf g n.2⟩ : FixedPoints.subgroup N A))
    fun g g' hgg' ↦ Subtype.ext <| by
      rw [QuotientGroup.leftRel_apply] at hgg'
      simpa using (apply_mul_of_mem hf g hgg').symm
  continuous_toFun := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr <|
    f.continuous.subtype_mk _
  map_mul' q q' := by
    induction q using QuotientGroup.induction_on with | H g =>
    induction q' using QuotientGroup.induction_on with | H g' =>
    exact Subtype.ext (f.apply_mul g g')

@[simp]
theorem coe_descend_apply (hf : ∀ n ∈ N, f n = 1) (g : G) :
    (f.descend N hf (g : G ⧸ N) : A) = f g :=
  (rfl)

/-- Inflating the descended cocycle recovers the original cocycle. -/
@[simp]
theorem map_descend (hf : ∀ n ∈ N, f n = 1) :
    (f.descend N hf).map (Subgroup.quotientMkContinuousMonoidHom N)
      (ContinuousMonoidHom.subgroupSubtype _) (subgroupSubtype_quotientMk_smul N) = f :=
  ext fun g ↦ by simp

end Cocycle

/-- The class of a cocycle trivial on `N` is the inflation of the class of its descent. -/
theorem infl_mk_descend (f : Cocycle G A) (hf : ∀ n ∈ N, f n = 1) :
    infl N (mk (f.descend N hf)) = mk f := by
  rw [infl_mk, Cocycle.map_descend]

/-- **Inflation is injective**: for every normal subgroup `N` of `G`, the map
`H¹(G ⧸ N, Aᴺ) → H¹(G, A)` is injective. No continuity of the multiplication of `A` or of the
action of `G` on `A` is needed. -/
theorem infl_injective : Function.Injective (infl (A := A) N) := by
  intro c₁ c₂ h
  induction c₁ using induction_on with | mk f₁ =>
  induction c₂ using induction_on with | mk f₂ =>
  rw [infl_mk, infl_mk] at h
  obtain ⟨a, ha⟩ := mk_eq_mk_iff.mp h
  -- The cocycle identity at the elements of `N` forces the witness `a` into `Aᴺ`.
  have haN : a ∈ FixedPoints.subgroup N A := fun n ↦ by
    have hn := ha n
    simp only [Cocycle.map_apply, Subgroup.quotientMkContinuousMonoidHom_apply,
      (QuotientGroup.eq_one_iff (n : G)).mpr n.2, Cocycle.apply_one,
      ContinuousMonoidHom.subgroupSubtype_apply, OneMemClass.coe_one, mul_one] at hn
    rw [eq_comm, inv_mul_eq_one] at hn
    exact hn.symm
  refine mk_eq_mk_iff.mpr ⟨⟨a, haN⟩, fun q ↦ ?_⟩
  induction q using QuotientGroup.induction_on with | H g =>
  exact Subtype.ext (by simpa using ha g)

/-- The restriction to `N` of an inflated class is the base point. -/
@[simp]
theorem res_infl (c : NonabelianH1 (G ⧸ N) (FixedPoints.subgroup N A)) : res N (infl N c) = 1 := by
  induction c using induction_on with | mk f =>
  rw [infl_mk, res_mk, mk_eq_one_iff]
  refine ⟨1, fun n ↦ ?_⟩
  simp [(QuotientGroup.eq_one_iff (n : G)).mpr n.2]

/-- **Inflation–restriction**: a class restricts to the base point of `H¹(N, A)` exactly when it is
inflated from `H¹(G ⧸ N, Aᴺ)`. -/
theorem res_eq_one_iff [ContinuousMul A] [ContinuousSMul G A] {c : NonabelianH1 G A} :
    res N c = 1 ↔ c ∈ Set.range (infl N) := by
  refine ⟨fun h ↦ ?_, fun ⟨c', hc'⟩ ↦ hc' ▸ res_infl N c'⟩
  induction c using induction_on with | mk f =>
  rw [res_mk] at h
  obtain ⟨a, ha⟩ := mk_eq_one_iff.mp h
  -- Twisting by `a⁻¹` makes the cocycle trivial on `N`, so that it descends to `G ⧸ N`.
  have hf : ∀ n ∈ N, f.twist a⁻¹ n = 1 := fun n hn ↦ by
    have hn := ha ⟨n, hn⟩
    simp only [Cocycle.map_apply, ContinuousMonoidHom.subgroupSubtype_apply,
      ContinuousMonoidHom.id_toFun] at hn
    rw [Cocycle.twist_apply, hn]
    simp [smul_inv']
  exact ⟨mk ((f.twist a⁻¹).descend N hf), by rw [infl_mk_descend, mk_twist]⟩

/-- **Reduction to finite quotients**: for `G` compact and `A` discrete, every class of
`H¹(G, A)` is inflated from `G ⧸ U` for an open normal subgroup `U`. Such a quotient is finite
(`Subgroup.quotient_finite_of_isOpen`). -/
theorem exists_mem_range_infl [IsTopologicalGroup G] [CompactSpace G] [DiscreteTopology A]
    (c : NonabelianH1 G A) : ∃ U : OpenNormalSubgroup G, c ∈ Set.range (infl U.toSubgroup) := by
  induction c using induction_on with | mk f =>
  obtain ⟨U, hU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    ((isClopen_discrete {1}).preimage f.continuous) (by simp)
  exact ⟨U, mk (f.descend U.toSubgroup fun _ hn ↦ hU hn), infl_mk_descend _ _ _⟩

end NonabelianH1

end TauCeti
