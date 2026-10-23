/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Congruence
public import TauCeti.Topology.Algebra.Group.ContinuousAut.ConjClasses

/-!
# The outer action of an extension

Let `E` be a topological group and `N` a normal subgroup of `E`, with the subspace topology.
Conjugation gives `ContinuousAut.conjNormal : E →* ContinuousAut N`, where `conjNormal e` sends `n`
to `e * n * e⁻¹`. Conjugation by an element of `N` is an inner automorphism of `N`
(`ContinuousAut.conjNormal_coe`), so composing
with the quotient map to `ContinuousOut N` kills `N`, and the result descends to the **outer
action** `TauCeti.outerAction : E ⧸ N →* ContinuousOut N`, sending `e N` to the class of
conjugation by `e` (`TauCeti.outerAction_mk`). Its kernel is the image of `N ⊔ C_E(N)`: the classes
of the elements of `E` that act on `N` as an element of `N` does.

When `N` is compact, `ContinuousAut.conjNormal` is continuous for the congruence topology on
`ContinuousAut N`: on each characteristic open quotient `N ⧸ U`, which is finite, the induced
automorphism is determined by the classes `e * n * e⁻¹ U` of finitely many representatives `n`,
each locally constant in `e`. Hence the outer action is continuous for the quotient topologies.
Neither finite generation nor total disconnectedness of `N` is needed for continuity; they are what
make `ContinuousAut N` and `ContinuousOut N` profinite.

The case of interest is a closed normal subgroup of a profinite group, such as the geometric
fundamental group inside an arithmetic fundamental group, where the outer action is the outer
Galois action. The construction does not use closedness, so no closedness hypothesis is imposed.

## Main definitions

* `TauCeti.outerAction`: the outer action `E ⧸ N →* ContinuousOut N`.

## Main results

* `TauCeti.outerAction_mk`: the outer action of `e N` is the class of conjugation by `e`.
* `TauCeti.ker_outerAction`: the kernel of the outer action is the image of `N ⊔ C_E(N)`.
* `TauCeti.outerAction_smul_conjClasses_mk`: the outer action on conjugacy classes of `N` is
  induced by conjugation.
* `TauCeti.ContinuousAut.continuous_conjNormal`, `TauCeti.continuous_outerAction`: for compact `N`,
  both maps are continuous for the congruence topology and its quotient.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

namespace TauCeti

variable {E : Type*} [Group E] [TopologicalSpace E] {N : Subgroup E} [N.Normal]

section Algebraic

variable [SeparatelyContinuousMul E]

variable (N) in
/-- The **outer action** of `E ⧸ N` on a normal subgroup `N`: the class of `e` acts by the outer
class of conjugation by `e` (`outerAction_mk`). It is well defined because conjugation by an
element of `N` is inner. -/
def outerAction : E ⧸ N →* ContinuousOut N :=
  QuotientGroup.lift N (ContinuousOut.mk.comp ContinuousAut.conjNormal) fun n hn ↦
    (congrArg ContinuousOut.mk (ContinuousAut.conjNormal_coe ⟨n, hn⟩)).trans
      (ContinuousOut.mk_conj _)

/-- The outer action of the class of `e` is the outer class of conjugation by `e`. -/
@[simp]
theorem outerAction_mk (e : E) :
    outerAction N (e : E ⧸ N) =
      ((ContinuousAut.conjNormal e : ContinuousAut N) : ContinuousOut N) :=
  (rfl)

/-- The kernel of the outer action is the image of `N ⊔ C_E(N)`: the class of `e` acts trivially
exactly when conjugation by `e` agrees on `N` with conjugation by an element of `N`. -/
theorem ker_outerAction :
    (outerAction N).ker = (N ⊔ Subgroup.centralizer (N : Set E)).map (QuotientGroup.mk' N) := by
  ext q
  obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker, outerAction_mk, QuotientGroup.eq_one_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨e, Subgroup.mem_sup_of_normal_left.mpr ⟨n, n.2, (n : E)⁻¹ * e, ?_, by group⟩, rfl⟩
    rw [← ContinuousAut.ker_conjNormal, MonoidHom.mem_ker, map_mul, map_inv,
      ContinuousAut.conjNormal_coe, hn, inv_mul_cancel]
  · rintro ⟨x, hx, hxe⟩
    obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hxe
    rw [← ContinuousAut.ker_conjNormal, MonoidHom.mem_ker] at hc
    -- `e = n * c * m` with `n, m ∈ N` and `c` centralizing `N`.
    have he : e = ((⟨n, hn⟩ : N) : E) * c * ((⟨_, hxe⟩ : N) : E) := by simp [mul_assoc]
    refine ⟨⟨n, hn⟩ * ⟨_, hxe⟩, ?_⟩
    conv_rhs => rw [he]
    rw [map_mul, map_mul, map_mul, hc, mul_one, ContinuousAut.conjNormal_coe,
      ContinuousAut.conjNormal_coe]

/-- The outer action on conjugacy classes of `N` is induced by conjugation: the class of `e` sends
the conjugacy class of `n` to that of `e * n * e⁻¹`. -/
theorem outerAction_smul_conjClasses_mk (e : E) (n : N) :
    outerAction N (e : E ⧸ N) • ConjClasses.mk n =
      ConjClasses.mk (ContinuousAut.conjNormal e n) := by
  rw [outerAction_mk, ContinuousOut.mk_smul_mk]

end Algebraic

section Continuity

variable [IsTopologicalGroup E] [CompactSpace N]

/-- For compact `N`, conjugation `E → ContinuousAut N` is continuous for the congruence topology:
on each characteristic open quotient `N ⧸ U`, which is finite, the induced automorphism is
determined by the locally constant classes of `e * n * e⁻¹` for finitely many `n`. -/
theorem ContinuousAut.continuous_conjNormal : Continuous (conjNormal : E → ContinuousAut N) := by
  refine continuous_iff_forall_continuous_mapQuotient.mpr fun ⟨U, hU⟩ ↦ ?_
  let _ : TopologicalSpace (MulAut (N ⧸ (U : Subgroup N))) := ⊥
  have := discreteTopology_bot (MulAut (N ⧸ (U : Subgroup N)))
  have := QuotientGroup.discreteTopology U.isOpen
  have : Finite (N ⧸ (U : Subgroup N)) := Subgroup.quotient_finite_of_isOpen _ U.isOpen
  -- Each class `e * n * e⁻¹ U` is continuous, hence locally constant, in `e`.
  have hcont (n : N) : Continuous fun e : E ↦ (conjNormal e n : N ⧸ (U : Subgroup N)) :=
    QuotientGroup.continuous_mk.comp <| continuous_induced_rng.mpr <|
      ((continuous_id.mul continuous_const).mul continuous_inv).congr fun e ↦
        (conjNormal_apply e n).symm
  refine ((mapQuotient hU).comp conjNormal).continuous_iff_isOpen_ker.mpr ?_
  have hker : (((mapQuotient hU).comp conjNormal).ker : Set E) =
      ⋂ q : N ⧸ (U : Subgroup N), {e | (conjNormal e q.out : N ⧸ (U : Subgroup N)) = q} := by
    ext e
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.ext_iff,
      MulAut.one_apply, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h q ↦ ?_, fun h q ↦ ?_⟩
    · rw [← mapQuotient_mk hU, QuotientGroup.out_eq', h]
    · conv_lhs => rw [← QuotientGroup.out_eq' q]
      rw [mapQuotient_mk, h]
  rw [hker]
  exact isOpen_iInter_of_finite fun q ↦ (hcont q.out).isOpen_preimage {q} (isOpen_discrete _)

/-- For compact `N`, the outer action `E ⧸ N → ContinuousOut N` is continuous for the quotient
topologies. -/
theorem continuous_outerAction : Continuous (outerAction N) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <|
    (QuotientGroup.continuous_mk.comp ContinuousAut.continuous_conjNormal).congr
      fun e ↦ (outerAction_mk e).symm

end Continuity

end TauCeti
