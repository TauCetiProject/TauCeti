/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Irreducible.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree

/-!
# A system of two commutators whose coordinate group is not fully residually free

Over a group `G`, consider the system `S = {[u, v], [u, x]}` in three variables `u`, `v`, `x`:
the equation `[u, v] = 1` in the variables `u`, `v`, below the quadratic equation
`x⁻¹ u x = u` in the variable `x`, whose coefficient `u` is a variable of the lower equation.
Each equation has a solution over the coordinate group of the equations below it (`x = 1`, and
`u = v = 1`), so `S` is a nondegenerate triangular quasi-quadratic system in the sense of
[VAR-II, Definition 8]. In the encoding `TauCeti.LimitGroup.NTQ.System`, the system with lower
level `[u, v] = 1` of type (3) and upper level `x⁻¹ u x u⁻¹ = 1` has the same solutions as `S`,
up to renaming the variables, and it is nondegenerate by
`TauCeti.LimitGroup.NTQ.isNondegenerate_conj_over_commute`. Nevertheless, over a nonabelian
group the coordinate group of `S` is not fully residually free.

The reason is commutation transitivity. A solution of `S` in a commutative transitive group either
has `u = 1`, which leaves `v` and `x` free, or makes `u`, `v` and `x` commute pairwise. In the
coordinate group of `S` over a nonabelian group, `u` and `[v, x]` both survive, so the class of
`u` is a nonidentity element commuting with two elements that do not commute.

## Main definitions

* `TauCeti.LimitGroup.NTQ.commutatorPair`: the system `{[u, v], [u, x]}` over `G`.

## Main results

Let `ι : G →* H` be the coefficient homomorphism and `S = commutatorPair G`.

* `V_commutatorPair_eq_union`: if `H` is commutative transitive, then
  `V_H(S) = V_H(u) ∪ V_H(S ∪ {[v, x]})`.
* `V_singleton_ssubset_V_commutatorPair`, `V_insert_ssubset_V_commutatorPair`: both pieces are
  proper, the first if `H` is nontrivial and the second if `H` is not commutative.
* `not_isIrreducible_V_commutatorPair`: `V_H(S)` is reducible if `H` is commutative transitive
  and not commutative.
* `inr_of_zero_notMem_Rad_commutatorPair`, `commutatorElement_notMem_Rad_commutatorPair`: the
  elements `u` and `[v, x]` do not lie in the radical of `S`.
* `map_commutatorElement_commutatorPair_eq_one`: every homomorphism from the coordinate group of
  `S` to a commutative transitive group that does not kill `u` kills `[v, x]`.
* `not_isCommTransitive_coordGroup_commutatorPair`,
  `not_isFullyResiduallyFree_coordGroup_commutatorPair`: if `H` is not commutative, the
  coordinate group of `S` over `H` is not commutative transitive, hence not fully residually
  free.
* `not_isDiscriminatedBy_coordGroup_commutatorPair`: if `H` is moreover commutative transitive, the
  coordinate group of `S` is not discriminated by `H`.

All hypotheses on `H` hold for a nonabelian free group, in particular for `H = G = F(a, b)`.

## References

* [VAR-II] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group II.
  Systems in triangular quasi-quadratic form and description of residually free groups*,
  J. Algebra 200 (1998), §0, Definition 8.
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.6 (commutation transitivity).
-/

public section

open Monoid.Coprod Group
open FreeGroup (of)
open scoped commutatorElement

namespace TauCeti.LimitGroup.NTQ

open GroupAlgGeom

variable {G H : Type*} [Group G] [Group H] {ι : G →* H}

variable (G) in
/-- The system `[u, v] = 1`, `[u, x] = 1` over `G` in the three variables `u`, `v`, `x`,
numbered `0`, `1`, `2`. -/
def commutatorPair : Set (GX G (Fin 3)) :=
  {⁅(inr (of 0) : GX G (Fin 3)), inr (of 1)⁆, ⁅(inr (of 0) : GX G (Fin 3)), inr (of 2)⁆}

variable (G) in
theorem commutatorPair_def : commutatorPair G =
    {⁅(inr (of 0) : GX G (Fin 3)), inr (of 1)⁆, ⁅(inr (of 0) : GX G (Fin 3)), inr (of 2)⁆} :=
  (rfl)

@[simp]
theorem mem_commutatorPair {w : GX G (Fin 3)} : w ∈ commutatorPair G ↔
    w = ⁅(inr (of 0) : GX G (Fin 3)), inr (of 1)⁆ ∨
      w = ⁅(inr (of 0) : GX G (Fin 3)), inr (of 2)⁆ :=
  Iff.rfl

/-- A triple `(u, v, x)` solves the system `[u, v] = 1`, `[u, x] = 1` exactly when `u` commutes
with `v` and with `x`. -/
@[simp high]
theorem mem_V_commutatorPair {p : Fin 3 → H} :
    p ∈ V ι (commutatorPair G) ↔ Commute (p 0) (p 1) ∧ Commute (p 0) (p 2) := by
  simp [commutatorElement_eq_one_iff_commute]

private theorem mem_V_insert_commutatorPair {p : Fin 3 → H} :
    p ∈ V ι (insert ⁅(inr (of 1) : GX G (Fin 3)), inr (of 2)⁆ (commutatorPair G)) ↔
      Commute (p 1) (p 2) ∧ p ∈ V ι (commutatorPair G) := by
  simp [commutatorElement_eq_one_iff_commute]

/-- Over a commutative transitive group, a solution of `[u, v] = 1`, `[u, x] = 1` either has
`u = 1` or solves `[v, x] = 1` as well. -/
theorem V_commutatorPair_eq_union (hH : IsCommTransitive H) :
    V ι (commutatorPair G) = V ι {inr (of 0)} ∪
      V ι (insert ⁅(inr (of 1) : GX G (Fin 3)), inr (of 2)⁆ (commutatorPair G)) := by
  ext p
  simp only [Set.mem_union, mem_V_insert_commutatorPair, mem_V_commutatorPair]
  simp only [mem_V, Set.mem_singleton_iff, forall_eq, eval_inr, FreeGroup.lift_apply_of]
  exact ⟨fun ⟨h1, h2⟩ => or_iff_not_imp_left.2 fun h0 =>
    ⟨(isCommTransitive_iff H).1 hH _ _ _ h0 h1.symm h2, h1, h2⟩,
    fun h => h.elim (fun h0 => by simp [h0]) And.right⟩

/-- Over a nontrivial group, the solutions of `[u, v] = 1`, `[u, x] = 1` with `u = 1` form a
proper subset of the solution set. -/
theorem V_singleton_ssubset_V_commutatorPair [Nontrivial H] :
    V ι {(inr (of 0) : GX G (Fin 3))} ⊂ V ι (commutatorPair G) := by
  obtain ⟨h, hh⟩ := exists_ne (1 : H)
  exact (Set.ssubset_iff_of_subset fun p hp => by simp_all).2
    ⟨![h, 1, 1], by simp, by simpa using hh⟩

/-- Over a group that is not commutative, the solutions of `[u, v] = 1`, `[u, x] = 1` with
`[v, x] = 1` form a proper subset of the solution set. -/
theorem V_insert_ssubset_V_commutatorPair (hH : ¬IsMulCommutative H) :
    V ι (insert ⁅(inr (of 1) : GX G (Fin 3)), inr (of 2)⁆ (commutatorPair G)) ⊂
      V ι (commutatorPair G) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : H, ¬Commute a b := by
    simpa [isMulCommutative_iff, Commute, SemiconjBy] using hH
  refine (Set.ssubset_iff_of_subset (V_antitone ι (Set.subset_insert _ _))).2
    ⟨![1, a, b], by simp, fun h => hab (mem_V_insert_commutatorPair.1 h).1⟩

/-- Over a commutative transitive group that is not commutative, the solution set of
`[u, v] = 1`, `[u, x] = 1` is reducible in the Zariski topology. -/
theorem not_isIrreducible_V_commutatorPair (hH : IsCommTransitive H) (hH' : ¬IsMulCommutative H) :
    ¬@IsIrreducible (Fin 3 → H) (zariskiTopology ι (Fin 3)) (V ι (commutatorPair G)) := by
  let := zariskiTopology ι (Fin 3)
  have : Nontrivial H := not_subsingleton_iff_nontrivial.1 fun _ =>
    hH' (.of_comm fun _ _ => Subsingleton.elim _ _)
  intro h
  rcases (isPreirreducible_iff_isClosed_union_isClosed.1 h.isPreirreducible) _ _
    (isClosed_V _) (isClosed_V _) (V_commutatorPair_eq_union hH).subset with h' | h'
  · exact V_singleton_ssubset_V_commutatorPair.not_subset h'
  · exact (V_insert_ssubset_V_commutatorPair hH').not_subset h'

/-- Over a nontrivial group, the variable `u` is not in the radical of `[u, v] = 1`,
`[u, x] = 1`. -/
theorem inr_of_zero_notMem_Rad_commutatorPair [Nontrivial H] :
    inr (of 0) ∉ Rad ι (commutatorPair G) := fun h =>
  V_singleton_ssubset_V_commutatorPair.not_subset fun p hp => by simpa using mem_Rad.1 h p hp

/-- Over a group that is not commutative, `[v, x]` is not in the radical of `[u, v] = 1`,
`[u, x] = 1`. -/
theorem commutatorElement_notMem_Rad_commutatorPair (hH : ¬IsMulCommutative H) :
    ⁅(inr (of 1) : GX G (Fin 3)), inr (of 2)⁆ ∉ Rad ι (commutatorPair G) := fun h =>
  (V_insert_ssubset_V_commutatorPair hH).not_subset fun p hp =>
    mem_V_insert_commutatorPair.2 ⟨by
      simpa [commutatorElement_eq_one_iff_commute] using mem_Rad.1 h p hp, hp⟩

/-- A homomorphism from the coordinate group of `[u, v] = 1`, `[u, x] = 1` to a commutative
transitive group that does not kill `u` kills `[v, x]`. -/
theorem map_commutatorElement_commutatorPair_eq_one {L : Type*} [Group L] (hL : IsCommTransitive L)
    (φ : CoordGroup ι (commutatorPair G) →* L) (hφ : φ (inr (of 0) : GX G (Fin 3)) ≠ 1) :
    φ (⁅(inr (of 1) : GX G (Fin 3)), inr (of 2)⁆ : GX G (Fin 3)) = 1 := by
  -- The quotient map is a homomorphism, so it commutes with commutators.
  have hmk (a b : GX G (Fin 3)) :
      ((⁅a, b⁆ : GX G (Fin 3)) : CoordGroup ι (commutatorPair G)) =
        ⁅(a : CoordGroup ι (commutatorPair G)), (b : CoordGroup ι (commutatorPair G))⁆ :=
    map_commutatorElement (QuotientGroup.mk' _) a b
  have hc (a b : GX G (Fin 3)) (h : ⁅a, b⁆ ∈ commutatorPair G) :
      Commute (φ a) (φ b) := by
    refine (commutatorElement_eq_one_iff_commute.1 ?_).map φ
    rw [← hmk, QuotientGroup.eq_one_iff]
    exact subset_Rad _ h
  rw [hmk, map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact (isCommTransitive_iff L).1 hL _ _ _ hφ (hc _ _ (Or.inl rfl)).symm (hc _ _ (Or.inr rfl))

/-- Over a group that is not commutative, the coordinate group of `[u, v] = 1`, `[u, x] = 1`
is not commutative transitive: the class of `u` is a nonidentity element commuting with the
classes of `v` and `x`, which do not commute. -/
theorem not_isCommTransitive_coordGroup_commutatorPair (hH : ¬IsMulCommutative H) :
    ¬IsCommTransitive (CoordGroup ι (commutatorPair G)) := by
  have : Nontrivial H := not_subsingleton_iff_nontrivial.1 fun _ =>
    hH (.of_comm fun _ _ => Subsingleton.elim _ _)
  exact fun hK => commutatorElement_notMem_Rad_commutatorPair (ι := ι) hH <|
    (QuotientGroup.eq_one_iff _).1 <| map_commutatorElement_commutatorPair_eq_one hK (.id _)
      (mt (QuotientGroup.eq_one_iff _).1 inr_of_zero_notMem_Rad_commutatorPair)

/-- Over a group that is not commutative, the coordinate group of `[u, v] = 1`, `[u, x] = 1`
is not fully residually free. -/
theorem not_isFullyResiduallyFree_coordGroup_commutatorPair (hH : ¬IsMulCommutative H) :
    ¬IsFullyResiduallyFree (CoordGroup ι (commutatorPair G)) :=
  fun h => not_isCommTransitive_coordGroup_commutatorPair hH h.isCommTransitive

/-- Over a commutative transitive group `H` that is not commutative, the coordinate group of
`[u, v] = 1`, `[u, x] = 1` is not discriminated by `H`. -/
theorem not_isDiscriminatedBy_coordGroup_commutatorPair (hH : IsCommTransitive H)
    (hH' : ¬IsMulCommutative H) :
    ¬IsDiscriminatedBy (CoordGroup.coeff ι (commutatorPair G)) ι := fun h =>
  not_isIrreducible_V_commutatorPair hH hH' (isIrreducible_V_iff_isDiscriminatedBy.2 h)

/-! ### Over the free group of rank two -/

example : ¬IsFullyResiduallyFree
    (CoordGroup (.id (FreeGroup (Fin 2))) (commutatorPair (FreeGroup (Fin 2)))) :=
  not_isFullyResiduallyFree_coordGroup_commutatorPair fun h =>
    not_subsingleton (Fin 2) (FreeGroup.isMulCommutative_iff_subsingleton.1 h)

example : ¬IsDiscriminatedBy
    (CoordGroup.coeff (.id (FreeGroup (Fin 2))) (commutatorPair (FreeGroup (Fin 2))))
    (.id (FreeGroup (Fin 2))) :=
  not_isDiscriminatedBy_coordGroup_commutatorPair IsFreeGroup.isCommTransitive fun h =>
    not_subsingleton (Fin 2) (FreeGroup.isMulCommutative_iff_subsingleton.1 h)

example : ¬@IsIrreducible (Fin 3 → FreeGroup (Fin 2)) (zariskiTopology (.id _) (Fin 3))
    (V (.id (FreeGroup (Fin 2))) (commutatorPair (FreeGroup (Fin 2)))) :=
  not_isIrreducible_V_commutatorPair IsFreeGroup.isCommTransitive fun h =>
    not_subsingleton (Fin 2) (FreeGroup.isMulCommutative_iff_subsingleton.1 h)

end TauCeti.LimitGroup.NTQ
