/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.GroupTheory.Powerful
public import TauCeti.Topology.Algebra.Group.Heisenberg
public import TauCeti.Topology.Algebra.Group.Powerful
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
import Mathlib.Data.Nat.Choose.Dvd

/-!
# Powerful pro-`p` groups

This file complements `TauCeti.Topology.Algebra.Group.Powerful` (`TauCeti.closedPowerSubgroup` and
`TauCeti.IsPowerful`) with additional power-subgroup and powerfulness lemmas, non-powerful witnesses
(`DihedralGroup n` for `4 ∣ n` and `HeisenbergGroup (ZMod p)` for every prime `p`), and the
profinite pro-`p` lifting theory.

For a profinite powerful pro-`p` group (without finite generation), compactness lifts the finite
theory of `TauCeti.GroupTheory.Powerful` to prove: every element of `λ_k(G)` is a `p ^ k`-th power,
`λ_k(G) = closedPowerSubgroup (p ^ k) G`, each `λ_k(G)` is powerful and shifts the lower `p`-series
by `k`, `gradedPow p G k` is an additive surjection in every degree, and absence of `p`-torsion is
equivalent to bijectivity of every `gradedPow p G k` via torsion lifting (DDMS Lemma 4.2).

## Main results

* `TauCeti.closedPowerSubgroup_prod`, `TauCeti.closedPowerSubgroup_pi`,
  `TauCeti.IsPowerful.pi`: product compatibility for closed power subgroups and powerfulness.
* `TauCeti.commutator_le_closedPowerSubgroup_two_dihedralGroup`,
  `TauCeti.not_isPowerful_two_dihedralGroup`, `TauCeti.not_isPowerful_heisenbergGroup_zmod`:
  non-powerful witnesses showing the fourth-power condition at `p = 2` and non-powerful finite
  `p`-groups for every prime `p`.
* `TauCeti.IsProP.mem_pLowerCentralSeries_iff_exists_pow_pow`,
  `TauCeti.IsProP.pLowerCentralSeries_eq_closedPowerSubgroup`,
  `TauCeti.IsProP.proPFrattini_eq_closedPowerSubgroup`: DDMS Theorem 3.6(ii)–(iii).
* `TauCeti.IsProP.isPowerful_pLowerCentralSeries`,
  `TauCeti.IsProP.map_subtype_pLowerCentralSeries_pLowerCentralSeries`: DDMS Theorem 3.6(i), (iv).
* `TauCeti.IsProP.gradedPow_add`, `TauCeti.IsProP.gradedPow_surjective`,
  `TauCeti.IsProP.antitone_natCard_gradedPiece`: DDMS Lemma 3.4.
* `TauCeti.IsProP.exists_pow_eq_one_of_notMem_pLowerCentralSeries_one`,
  `TauCeti.IsProP.forall_eq_one_of_pow_eq_one_iff_injective_gradedPow`,
  `TauCeti.IsProP.forall_eq_one_of_pow_eq_one_iff_bijective_gradedPow`: DDMS Lemma 4.2 and
  torsion-free characterization of graded `p`-power bijectivity.

## References

* J. D. Dixon, M. P. F. du Sautoy, A. Mann, and D. Segal, *Analytic pro-`p` groups*, 2nd ed.,
  Chapter 3 (Lemma 3.4, Theorem 3.6) and Chapter 4 (Lemma 4.2, Theorem 4.5).
-/

public section

namespace TauCeti

open Subgroup
open scoped commutatorElement

universe u v

/-! ### Additional closed power subgroup lemmas -/

section ClosedPowerSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `closedPowerSubgroup n G` is the topological closure of `(⊤ : Subgroup G).powClosure n`. -/
theorem closedPowerSubgroup_eq_topologicalClosure_powClosure (n : ℕ) :
    closedPowerSubgroup n G = ((⊤ : Subgroup G).powClosure n).topologicalClosure := by
  rw [closedPowerSubgroup_eq_topologicalClosure, Subgroup.powClosure_top]

variable {G}

/-- In a `T1` topological group, `closedPowerSubgroup 0 G = ⊥`. -/
@[simp]
theorem closedPowerSubgroup_zero [T1Space G] : closedPowerSubgroup 0 G = ⊥ :=
  le_bot_iff.mp <| (closedPowerSubgroup_le_iff (by simp)).mpr fun _ ↦ by simp

/-- In a subsingleton topological group, every closed power subgroup is `⊤`. -/
theorem closedPowerSubgroup_of_subsingleton [Subsingleton G] (n : ℕ) :
    closedPowerSubgroup n G = ⊤ :=
  Subsingleton.elim _ _

/-- On a discrete group, `closedPowerSubgroup n G` agrees with `(⊤ : Subgroup G).powClosure n`. -/
theorem closedPowerSubgroup_eq_of_discreteTopology [DiscreteTopology G] (n : ℕ) :
    closedPowerSubgroup n G = (⊤ : Subgroup G).powClosure n := by
  rw [closedPowerSubgroup_eq_topologicalClosure_powClosure]
  exact le_antisymm (topologicalClosure_minimal _ le_rfl (isClosed_discrete _))
    (le_topologicalClosure _)

section Functoriality

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Every closed power subgroup is topologically characteristic. -/
theorem isTopCharacteristic_closedPowerSubgroup (n : ℕ) :
    IsTopCharacteristic G (closedPowerSubgroup n G) :=
  isTopCharacteristic_iff_map_eq.mpr fun φ ↦ φ.map_closedPowerSubgroup_eq

/-- The closed `n`-th power subgroup of a product is the product of the closed `n`-th power
subgroups. -/
theorem closedPowerSubgroup_prod (n : ℕ) :
    closedPowerSubgroup n (G × H) = (closedPowerSubgroup n G).prod (closedPowerSubgroup n H) :=
  le_antisymm
    ((closedPowerSubgroup_le_iff (by
      rw [coe_prod]
      exact (isClosed_closedPowerSubgroup).prod (isClosed_closedPowerSubgroup))).mpr fun x ↦
      ⟨pow_mem_closedPowerSubgroup x.1, pow_mem_closedPowerSubgroup x.2⟩)
    prod_closedPowerSubgroup_le

/-- The closed `n`-th power subgroup of an arbitrary product is the product of the closed `n`-th
power subgroups. -/
theorem closedPowerSubgroup_pi {ι : Type*} {F : ι → Type*} [∀ i, Group (F i)]
    [∀ i, TopologicalSpace (F i)] [∀ i, IsTopologicalGroup (F i)] (n : ℕ) :
    closedPowerSubgroup n (∀ i, F i) =
      Subgroup.pi Set.univ (fun i ↦ closedPowerSubgroup n (F i)) := by
  classical
  refine le_antisymm ((closedPowerSubgroup_le_iff (by
    rw [coe_pi]; exact isClosed_set_pi fun _ _ ↦ isClosed_closedPowerSubgroup)).mpr
      fun x i _ ↦ pow_mem_closedPowerSubgroup (x i)) fun x hx ↦ ?_
  rw [← SetLike.mem_coe, ← (isClosed_closedPowerSubgroup (n := n) (G := ∀ i, F i)).closure_eq,
    mem_closure_iff]
  intro V hV hxV
  obtain ⟨I, t, ht, htV⟩ := isOpen_pi_iff.mp hV x hxV
  refine ⟨fun i ↦ if i ∈ I then x i else 1,
    htV fun i hi ↦ by simpa [Finset.mem_coe.mp hi] using (ht i (Finset.mem_coe.mp hi)).2,
    Submonoid.pi_mem_of_mulSingle_mem_aux I _ (fun i hi ↦ by simp [hi]) fun i hi ↦ by
      simpa [hi] using (MonoidHom.mulSingle F i).map_closedPowerSubgroup_le
        (continuous_mulSingle i) ⟨x i, hx i (Set.mem_univ i), rfl⟩⟩

end Functoriality

end ClosedPowerSubgroup

/-! ### Additional powerful group lemmas -/

section Powerful

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every subsingleton topological group is powerful for every `p`. -/
theorem isPowerful_of_subsingleton [Subsingleton G] : IsPowerful p G :=
  isPowerful_of_isMulCommutative

/-- On a discrete group, `IsPowerful p G` agrees with `(⊤ : Subgroup G).IsPowerfullyEmbedded p`. -/
theorem isPowerful_iff_isPowerfullyEmbedded_top [DiscreteTopology G] :
    IsPowerful p G ↔ (⊤ : Subgroup G).IsPowerfullyEmbedded p := by
  rw [isPowerful_iff, Subgroup.isPowerfullyEmbedded_iff, closedPowerSubgroup_eq_of_discreteTopology,
    commutator_def]
  exact ⟨fun h ↦ ⟨inferInstance, h⟩, fun h ↦ h.2⟩

namespace IsPowerful

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A quotient of a powerful group by a normal subgroup is powerful. -/
theorem quotient (hG : IsPowerful p G) (N : Subgroup G) [N.Normal] : IsPowerful p (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- A topological group isomorphism carries powerfulness to its target. -/
theorem of_equiv (hG : IsPowerful p G) (e : G ≃ₜ* H) : IsPowerful p H :=
  (isPowerful_congr e).mp hG

/-- An arbitrary product of powerful groups is powerful. -/
theorem pi {ι : Type*} {F : ι → Type*} [∀ i, Group (F i)] [∀ i, TopologicalSpace (F i)]
    [∀ i, IsTopologicalGroup (F i)] (hF : ∀ i, IsPowerful p (F i)) : IsPowerful p (∀ i, F i) := by
  rw [isPowerful_iff, closedPowerSubgroup_pi, commutator_def, Subgroup.commutator_le]
  exact fun x _ y _ i _ ↦ (isPowerful_iff.mp (hF i)) (commutator_def (F i) ▸
    commutator_mem_commutator (mem_top (x i)) (mem_top (y i)))

end IsPowerful

end Powerful

/-! ### Non-powerful witnesses -/

section Witnesses

/-- In every dihedral group `DihedralGroup n`, every commutator is a square, so
`[D_n, D_n] ≤ D_n²`. -/
theorem commutator_le_closedPowerSubgroup_two_dihedralGroup (n : ℕ)
    [TopologicalSpace (DihedralGroup n)] [DiscreteTopology (DihedralGroup n)] :
    ⁅(⊤ : Subgroup (DihedralGroup n)), ⊤⁆ ≤ closedPowerSubgroup 2 (DihedralGroup n) := by
  simpa [commutator_def] using
    (commutator_le_closedPowerSubgroup_two (G := DihedralGroup n))

/-- Whenever `4 ∣ n`, `DihedralGroup n` is not powerful at `p = 2`: every fourth power is a
rotation by a multiple of `4`, whereas `[r 1, sr 0] = r 2`. Together with
`TauCeti.commutator_le_closedPowerSubgroup_two_dihedralGroup`, this shows why the fourth-power
condition at `p = 2` is strictly stronger than `[G, G] ≤ G²`. -/
theorem not_isPowerful_two_dihedralGroup {n : ℕ} (hn : 4 ∣ n)
    [TopologicalSpace (DihedralGroup n)] [DiscreteTopology (DihedralGroup n)] :
    ¬ IsPowerful 2 (DihedralGroup n) := fun hpow ↦ by
  let K : Subgroup (DihedralGroup n) :=
    { carrier := {g | ∃ i : ZMod n, g = DihedralGroup.r (4 * i)}
      mul_mem' := by rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩; exact ⟨i + j, by simp [mul_add]⟩
      one_mem' := ⟨0, by simp⟩
      inv_mem' := by rintro _ ⟨i, rfl⟩; exact ⟨-i, by simp [mul_neg]⟩ }
  have h4le : closedPowerSubgroup 4 (DihedralGroup n) ≤ K :=
    (closedPowerSubgroup_le_iff (isClosed_discrete _)).mpr <| by
      rintro (i | i)
      · exact ⟨i, by rw [DihedralGroup.r_pow, Nat.cast_ofNat, mul_comm]⟩
      · exact ⟨0, by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]; simp [sq]⟩
  obtain ⟨i, hi⟩ := h4le (isPowerful_two_iff.mp hpow <| by
    rw [commutator_def]
    exact commutator_mem_commutator (mem_top (DihedralGroup.r (1 : ZMod n)))
      (mem_top (DihedralGroup.sr (0 : ZMod n))))
  have h2eq : (2 : ZMod n) = 4 * i :=
    DihedralGroup.r.inj ((by simp [commutatorElement_def]; ring :
      ⁅DihedralGroup.r (1 : ZMod n), DihedralGroup.sr (0 : ZMod n)⁆ = DihedralGroup.r 2).symm.trans
      hi)
  have h := congrArg (ZMod.castHom hn (ZMod 4)) h2eq
  rw [map_ofNat, map_mul, map_ofNat, show (4 : ZMod 4) = 0 from by decide, zero_mul] at h
  exact (by decide : (2 : ZMod 4) ≠ 0) h

/-- For every prime `p`, the finite Heisenberg group `HeisenbergGroup (ZMod p)` is not powerful
for `p`: every `p`-th power (or fourth power when `p = 2`) is trivial, while the commutator
`⁅(1, 0, 0), (0, 1, 0)⁆ = (0, 0, 1)` is nontrivial. -/
theorem not_isPowerful_heisenbergGroup_zmod (p : ℕ) [hp : Fact p.Prime] :
    ¬ IsPowerful p (HeisenbergGroup (ZMod p)) := fun hpow ↦ by
  set e : ℕ := if p = 2 then 4 else p
  have hpe : (p : ℕ) ∣ e := by by_cases hp2 : p = 2 <;> [subst hp2; simp [e, hp2]]; decide
  have hpe2 : (p : ℕ) ∣ e.choose 2 := by
    by_cases hp2 : p = 2
    · subst hp2; decide
    · simpa [e, hp2] using
        hp.out.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
  have hzero : ∀ (m : ℕ) (r : ZMod p), p ∣ m → m • r = 0 := fun m r ⟨c, hc⟩ ↦ by
    rw [hc, nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]
  have hbot : closedPowerSubgroup e (HeisenbergGroup (ZMod p)) = ⊥ :=
    le_bot_iff.mp ((closedPowerSubgroup_le_iff (isClosed_discrete _)).mpr fun a ↦ mem_bot.mpr <| by
      rw [HeisenbergGroup.pow_eq]; ext <;> simp [hzero e _ hpe, hzero (e.choose 2) _ hpe2])
  have h := congrArg HeisenbergGroup.z <| mem_bot.mp <| hbot ▸
    (isPowerful_iff.mp hpow) (commutator_def (HeisenbergGroup (ZMod p)) ▸
      commutator_mem_commutator (mem_top (⟨1, 0, 0⟩ : HeisenbergGroup (ZMod p)))
        (mem_top (⟨0, 1, 0⟩ : HeisenbergGroup (ZMod p))))
  simp [HeisenbergGroup.commutatorElement_eq] at h

end Witnesses

/-! ### Powerful profinite pro-`p` groups -/

section ProfiniteProP

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

namespace IsProP

omit hp [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem quotient_openNormalSubgroup_isPowerfullyEmbedded (hpow : IsPowerful p G)
    (U : OpenNormalSubgroup G) :
    (⊤ : Subgroup (G ⧸ U.toSubgroup)).IsPowerfullyEmbedded p :=
  have := QuotientGroup.discreteTopology (hN := U.isOpen)
  isPowerful_iff_isPowerfullyEmbedded_top.mp (hpow.quotient U.toSubgroup)

omit hp [TotallyDisconnectedSpace G] in
private theorem map_pLowerCentralSeries_openNormalSubgroup (U : OpenNormalSubgroup G) (k : ℕ) :
    (pLowerCentralSeries p G k).map (QuotientGroup.mk' U.toSubgroup) =
      (⊤ : Subgroup (G ⧸ U.toSubgroup)).pLowerCentralSeries p k := by
  have := QuotientGroup.discreteTopology (hN := U.isOpen)
  rw [(QuotientGroup.mk' U.toSubgroup).map_pLowerCentralSeries_eq_of_surjective
      QuotientGroup.continuous_mk QuotientGroup.continuous_mk.isClosedMap
      (QuotientGroup.mk'_surjective _),
    pLowerCentralSeries_eq_of_discreteTopology]

/-- **Every element of `λ_k(G)` is a `p ^ k`-th power** (Dixon–du Sautoy–Mann–Segal,
Theorem 3.6(iii)): in a profinite powerful pro-`p` group `G`, the `k`-th term of the lower
`p`-series consists precisely of the `p ^ k`-th powers. No finite generation is needed. -/
theorem mem_pLowerCentralSeries_iff_exists_pow_pow (hG : IsProP p G) (hpow : IsPowerful p G)
    (k : ℕ) {g : G} :
    g ∈ pLowerCentralSeries p G k ↔ ∃ x : G, x ^ (p ^ k) = g := by
  refine ⟨fun hg ↦ ?_, fun ⟨x, hx⟩ ↦ hx ▸ by
    simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p x) k⟩
  let F : OpenNormalSubgroup G → Set G := fun U ↦
    {x : G | (x : G ⧸ U.toSubgroup) ^ (p ^ k) = (g : G ⧸ U.toSubgroup)}
  have hF_closed : ∀ U, IsClosed (F U) := fun U ↦
    have := QuotientGroup.discreteTopology (hN := U.isOpen)
    (isClosed_singleton (x := (g : G ⧸ U.toSubgroup))).preimage
      ((continuous_pow (p ^ k)).comp QuotientGroup.continuous_mk)
  have hF_nonempty : ∀ U, (F U).Nonempty := fun U ↦ by
    have := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
    have hgU : (g : G ⧸ U.toSubgroup) ∈
        (⊤ : Subgroup (G ⧸ U.toSubgroup)).pLowerCentralSeries p k :=
      map_pLowerCentralSeries_openNormalSubgroup U k ▸ ⟨g, hg, rfl⟩
    have hU := quotient_openNormalSubgroup_isPowerfullyEmbedded hpow U
    obtain ⟨xQ, hxQ⟩ :=
      (hU.mem_pLowerCentralSeries_iff_exists_pow_pow (isProP_iff.mp hG U) k).mp hgU
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xQ
    exact ⟨x, hxQ⟩
  have hF_dir : Directed (· ⊇ ·) F := fun U V ↦ ⟨U ⊓ V,
    fun _ hx ↦ by
      simpa [F, map_pow] using congrArg
        (QuotientGroup.mapOfLE (inf_le_left : (U ⊓ V).toSubgroup ≤ U.toSubgroup)) hx,
    fun _ hx ↦ by
      simpa [F, map_pow] using congrArg
        (QuotientGroup.mapOfLE (inf_le_right : (U ⊓ V).toSubgroup ≤ V.toSubgroup)) hx⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F hF_dir
    hF_nonempty (fun U ↦ (hF_closed U).isCompact) hF_closed
  refine ⟨x, eq_of_inv_mul_eq_one (Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U ↦ ?_)⟩
  exact QuotientGroup.eq.mp (by rw [QuotientGroup.mk_pow]; exact Set.mem_iInter.mp hx U)

/-- **The lower `p`-series equals the closed power subgroups** (Dixon–du Sautoy–Mann–Segal,
Theorem 3.6(ii)): in a profinite powerful pro-`p` group, `λ_k(G) = closedPowerSubgroup (p ^ k) G`.
No finite generation is needed. -/
theorem pLowerCentralSeries_eq_closedPowerSubgroup (hG : IsProP p G) (hpow : IsPowerful p G)
    (k : ℕ) : pLowerCentralSeries p G k = closedPowerSubgroup (p ^ k) G :=
  le_antisymm
    (fun _ hg ↦ let ⟨x, hx⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow k).mp hg
      hx ▸ pow_mem_closedPowerSubgroup x)
    ((closedPowerSubgroup_le_iff (isClosed_pLowerCentralSeries k)).mpr fun g ↦ by
      simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g) k)

/-- In a profinite powerful pro-`p` group, `λ_1(G) = closedPowerSubgroup p G`. -/
theorem pLowerCentralSeries_one_eq_closedPowerSubgroup (hG : IsProP p G) (hpow : IsPowerful p G) :
    pLowerCentralSeries p G 1 = closedPowerSubgroup p G := by
  simpa using hG.pLowerCentralSeries_eq_closedPowerSubgroup hpow 1

/-- In a profinite powerful pro-`p` group, the pro-`p` Frattini subgroup is
`closedPowerSubgroup p G`. -/
theorem proPFrattini_eq_closedPowerSubgroup (hG : IsProP p G) (hpow : IsPowerful p G) :
    proPFrattini p G = closedPowerSubgroup p G := by
  rw [← pLowerCentralSeries_one_eq_proPFrattini hp.out,
    hG.pLowerCentralSeries_one_eq_closedPowerSubgroup hpow]

/-- In a profinite powerful pro-`2` group, `⁅λ_k(G), G⁆ ≤ λ_{k+2}(G)` for every `k`. -/
theorem commutator_pLowerCentralSeries_top_le_add_two (hG : IsProP 2 G) (hpow : IsPowerful 2 G)
    (k : ℕ) :
    ⁅pLowerCentralSeries 2 G k, (⊤ : Subgroup G)⁆ ≤ pLowerCentralSeries 2 G (k + 2) := by
  rw [(pLowerCentralSeries 2 G (k + 2)).eq_iInf_sup_openNormalSubgroup
      (isClosed_pLowerCentralSeries (k + 2))]
  refine le_iInf fun U ↦ ?_
  have := U.toSubgroup.quotient_finite_of_isOpen U.isOpen
  have hmap : ⁅pLowerCentralSeries 2 G k, (⊤ : Subgroup G)⁆.map (QuotientGroup.mk' U.toSubgroup) ≤
      (pLowerCentralSeries 2 G (k + 2)).map (QuotientGroup.mk' U.toSubgroup) := by
    rw [map_commutator, map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
      map_pLowerCentralSeries_openNormalSubgroup U k,
      map_pLowerCentralSeries_openNormalSubgroup U (k + 2)]
    have hU := quotient_openNormalSubgroup_isPowerfullyEmbedded hpow U
    exact hU.commutator_pLowerCentralSeries_top_le_add_two (isProP_iff.mp hG U) k
  intro g hg
  obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp (hmap ⟨g, hg, rfl⟩)
  simpa using Subgroup.mul_mem_sup hh (QuotientGroup.eq.mp hgh)

/-- **Every term of the lower `p`-series is powerful** (Dixon–du Sautoy–Mann–Segal, Theorem 3.6(i)):
in a profinite powerful pro-`p` group `G`, each `λ_k(G)` is again powerful for `p`. -/
theorem isPowerful_pLowerCentralSeries (hG : IsProP p G) (hpow : IsPowerful p G) (k : ℕ) :
    IsPowerful p (pLowerCentralSeries p G k) := by
  rw [isPowerful_iff, commutator_def, commutator_le]
  rintro a _ b _
  set r : ℕ := if p = 2 then 2 else 1
  have he : p ^ r = if p = 2 then 4 else p := by by_cases hp2 : p = 2 <;> simp [r, hp2]
  have hab : ((⁅a, b⁆ : pLowerCentralSeries p G k) : G) ∈ pLowerCentralSeries p G (k + r) := by
    have hval : ((⁅a, b⁆ : pLowerCentralSeries p G k) : G) = ⁅(a : G), (b : G)⁆ :=
      map_commutatorElement (pLowerCentralSeries p G k).subtype a b
    rw [hval]
    by_cases hp2 : p = 2
    · subst hp2
      exact hG.commutator_pLowerCentralSeries_top_le_add_two hpow k
        (commutator_mem_commutator a.property (mem_top (b : G)))
    · simpa [r, hp2] using commutator_mem_pLowerCentralSeries_succ a.property (b : G)
  obtain ⟨x, hx⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow (k + r)).mp hab
  let y : pLowerCentralSeries p G k :=
    ⟨x ^ (p ^ k), (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow k).mpr ⟨x, rfl⟩⟩
  have hy : y ^ (if p = 2 then 4 else p) = ⁅a, b⁆ :=
    Subtype.ext <| by rw [coe_pow, ← he, ← pow_mul, ← pow_add]; exact hx
  exact hy ▸ pow_mem_closedPowerSubgroup y

/-- Every closed `p ^ k`-th power subgroup of a profinite powerful pro-`p` group is powerful. -/
theorem isPowerful_closedPowerSubgroup_pow (hG : IsProP p G) (hpow : IsPowerful p G) (k : ℕ) :
    IsPowerful p (closedPowerSubgroup (p ^ k) G) :=
  hG.pLowerCentralSeries_eq_closedPowerSubgroup hpow k ▸ hG.isPowerful_pLowerCentralSeries hpow k

/-- **Shift invariance of the lower `p`-series** (Dixon–du Sautoy–Mann–Segal, Theorem 3.6(iv)):
in a profinite powerful pro-`p` group `G`, the `j`-th term of the lower `p`-series of `λ_k(G)`
maps onto `λ_{k+j}(G)`. -/
theorem map_subtype_pLowerCentralSeries_pLowerCentralSeries (hG : IsProP p G)
    (hpow : IsPowerful p G) (k j : ℕ) :
    (pLowerCentralSeries p (pLowerCentralSeries p G k) j).map
        (pLowerCentralSeries p G k).subtype =
      pLowerCentralSeries p G (k + j) := by
  set H := pLowerCentralSeries p G k
  have hH_proP := hG.subgroup H
  have hH_pow := hG.isPowerful_pLowerCentralSeries hpow k
  ext g
  rw [mem_map, hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow (k + j)]
  refine ⟨?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := (hH_proP.mem_pLowerCentralSeries_iff_exists_pow_pow hH_pow j).mp hy
    obtain ⟨x, hx⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow k).mp z.property
    exact ⟨x, by rw [pow_add, pow_mul, hx, ← coe_pow]; rfl⟩
  · let z : H := ⟨x ^ (p ^ k), (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow k).mpr ⟨x, rfl⟩⟩
    exact ⟨z ^ (p ^ j), (hH_proP.mem_pLowerCentralSeries_iff_exists_pow_pow hH_pow j).mpr ⟨z, rfl⟩,
      by rw [← hx, coe_subtype, coe_pow, ← pow_mul, ← pow_add]⟩

/-! ### Graded `p`-power operator and torsion lifting -/

/-- **Additivity of the graded `p`-power operator** in every degree for a profinite powerful
pro-`p` group, including degree `0` at `p = 2`. -/
theorem gradedPow_add (hG : IsProP p G) (hpow : IsPowerful p G) (k : ℕ)
    (x y : gradedPiece p G k) :
    gradedPow p G k (x + y) = gradedPow p G k x + gradedPow p G k y := by
  cases k with
  | succ k => exact gradedPow_add_of_one_le (Nat.succ_le_succ (Nat.zero_le k)) x y
  | zero =>
    by_cases hp2 : p = 2
    · subst hp2
      rw [gradedPow_add_zero_of_two rfl]
      obtain ⟨a, rfl⟩ := gradedMkZero_surjective x
      obtain ⟨b, rfl⟩ := gradedMkZero_surjective y
      rw [gradedBracket_gradedMkZero, gradedMk_eq_zero_iff.mpr
        (hG.commutator_pLowerCentralSeries_top_le_add_two hpow 0
          (commutator_mem_commutator (mem_pLowerCentralSeries_zero 2 a) (mem_top b))), add_zero]
    · exact gradedPow_add_zero_of_odd (hp.out.odd_of_ne_two hp2) x y

/-- **Surjectivity of the graded `p`-power operator** (Dixon–du Sautoy–Mann–Segal, Lemma 3.4):
in a profinite powerful pro-`p` group, `gradedPow p G k : gr_k(G) → gr_{k+1}(G)` is surjective in
every degree `k`. -/
theorem gradedPow_surjective (hG : IsProP p G) (hpow : IsPowerful p G) (k : ℕ) :
    Function.Surjective (gradedPow p G k) := fun z ↦ by
  obtain ⟨⟨g, hg⟩, rfl⟩ := gradedMk_surjective (k + 1) z
  obtain ⟨x, rfl⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow (k + 1)).mp hg
  refine ⟨gradedMk p G k ⟨x ^ (p ^ k),
    (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow k).mpr ⟨x, rfl⟩⟩, ?_⟩
  rw [gradedPow_gradedMk]
  exact congrArg (gradedMk p G (k + 1)) (Subtype.ext (by simp [pow_succ, pow_mul]))

/-- In a topologically finitely generated profinite powerful pro-`p` group, the cardinalities of
the graded pieces `gr_k(G) = λ_k ⧸ λ_{k+1}` form a nonincreasing sequence. -/
theorem antitone_natCard_gradedPiece (hG : IsProP p G)
    (hfg : IsTopologicallyFinitelyGenerated G) (hpow : IsPowerful p G) :
    Antitone fun k ↦ Nat.card (gradedPiece p G k) :=
  antitone_nat_of_succ_le fun k ↦
    have := hfg.finite_gradedPiece hp.out k
    Nat.card_le_card_of_surjective (gradedPow p G k) (hG.gradedPow_surjective hpow k)

/-- **Multiplicativity of the `p`-th power map modulo `λ_{m+2}`** in a profinite powerful pro-`p`
group: for arbitrary `x : G` and `y ∈ λ_m(G)`, `(x * y) ^ p = x ^ p * y ^ p` in `G ⧸ λ_{m+2}(G)`,
for every prime `p`. -/
theorem mk_mul_pow_pLowerCentralSeries_add_two (hG : IsProP p G) (hpow : IsPowerful p G)
    (m : ℕ) (x : G) {y : G} (hy : y ∈ pLowerCentralSeries p G m) :
    ((x * y : G) : G ⧸ pLowerCentralSeries p G (m + 2)) ^ p =
      (x : G ⧸ pLowerCentralSeries p G (m + 2)) ^ p *
        (y : G ⧸ pLowerCentralSeries p G (m + 2)) ^ p := by
  set N := pLowerCentralSeries p G (m + 2)
  rw [QuotientGroup.mk_mul]
  by_cases hp2 : p = 2
  · subst hp2
    exact (QuotientGroup.commute_mk_iff.mpr <| inv_mem_iff.mp <| commutatorElement_inv x y ▸
      hG.commutator_pLowerCentralSeries_top_le_add_two hpow m
        (commutator_mem_commutator hy (mem_top x))).mul_pow 2
  · have hyx := commutator_mem_pLowerCentralSeries_succ hy x
    have hmk_comm : ⁅(y : G ⧸ N), (x : G ⧸ N)⁆ = ((⁅y, x⁆ : G) : G ⧸ N) :=
      (map_commutatorElement (QuotientGroup.mk' N) y x).symm
    obtain ⟨c, hc⟩ :=
      hp.out.dvd_choose_self two_ne_zero (lt_of_le_of_ne hp.out.two_le (Ne.symm hp2))
    have hpow_yx : (((⁅y, x⁆ : G) : G ⧸ N) ^ p) = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact pow_mem_pLowerCentralSeries hyx
    rw [Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
        (hmk_comm.symm ▸ commute_mk_of_mem_pLowerCentralSeries hyx x)
        (hmk_comm.symm ▸ commute_mk_of_mem_pLowerCentralSeries hyx y) p,
      hmk_comm, hc, pow_mul, hpow_yx, one_pow, mul_one]

/-- One step of the torsion-lifting iteration: if `x ^ p ∈ λ_{k+2}`, there exists `y ∈ λ_{k+1}`
such that `(x * y) ^ p ∈ λ_{k+3}`. -/
private theorem exists_mul_pow_mem_pLowerCentralSeries_add_three (hG : IsProP p G)
    (hpow : IsPowerful p G) (k : ℕ) {x : G} (hx : x ^ p ∈ pLowerCentralSeries p G (k + 2)) :
    ∃ y ∈ pLowerCentralSeries p G (k + 1), (x * y) ^ p ∈ pLowerCentralSeries p G (k + 3) := by
  obtain ⟨u, hu⟩ := (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow (k + 2)).mp (inv_mem hx)
  have hu1 : u ^ (p ^ (k + 1)) ∈ pLowerCentralSeries p G (k + 1) :=
    (hG.mem_pLowerCentralSeries_iff_exists_pow_pow hpow (k + 1)).mpr ⟨u, rfl⟩
  refine ⟨u ^ (p ^ (k + 1)), hu1, ?_⟩
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow,
    hG.mk_mul_pow_pLowerCentralSeries_add_two hpow (k + 1) x hu1,
    ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow, ← pow_mul, ← pow_succ, hu,
    ← QuotientGroup.mk_mul, mul_inv_cancel, QuotientGroup.mk_one]

/-- **Torsion lifting in a powerful pro-`p` group** (Dixon–du Sautoy–Mann–Segal, Lemma 4.2):
if an element `x ∉ λ_1(G)` satisfies `x ^ p ∈ λ_2(G)`, then `G` contains a nontrivial element `g`
of order `p` representing the same coset as `x` modulo `λ_1(G)`. No finite generation is needed. -/
theorem exists_pow_eq_one_of_notMem_pLowerCentralSeries_one (hG : IsProP p G)
    (hpow : IsPowerful p G) {x : G} (hx1 : x ∉ pLowerCentralSeries p G 1)
    (hx2 : x ^ p ∈ pLowerCentralSeries p G 2) :
    ∃ g : G, g ≠ 1 ∧ g ^ p = 1 ∧
      (g : G ⧸ pLowerCentralSeries p G 1) = (x : G ⧸ pLowerCentralSeries p G 1) := by
  let step : ∀ k, {z : G // z ^ p ∈ pLowerCentralSeries p G (k + 2)} →
      {z : G // z ^ p ∈ pLowerCentralSeries p G (k + 3)} := fun k s ↦
    let h := hG.exists_mul_pow_mem_pLowerCentralSeries_add_three hpow k s.property
    ⟨s.val * Classical.choose h, (Classical.choose_spec h).2⟩
  let seq : ∀ k, {z : G // z ^ p ∈ pLowerCentralSeries p G (k + 2)} := Nat.rec ⟨x, hx2⟩ step
  have hstep_eq : ∀ k, ((seq (k + 1)).val : G ⧸ pLowerCentralSeries p G (k + 1)) =
      ((seq k).val : G ⧸ pLowerCentralSeries p G (k + 1)) := fun k ↦ by
    have h := hG.exists_mul_pow_mem_pLowerCentralSeries_add_three hpow k (seq k).property
    dsimp only [seq, step]
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (Classical.choose_spec h).1, mul_one]
  obtain ⟨g, hg, -⟩ := hG.existsUnique_forall_mk_eq_pLowerCentralSeries hp.out
    (fun k ↦ ((seq k).val : G ⧸ pLowerCentralSeries p G k)) fun k z hz ↦ by
      simpa using congrArg (QuotientGroup.mapOfLE (pLowerCentralSeries_succ_le k))
        (hz.trans (hstep_eq k))
  have hgx : (g : G ⧸ pLowerCentralSeries p G 1) = (x : G ⧸ pLowerCentralSeries p G 1) := by
    simpa [seq] using (hg 1).trans (hstep_eq 0)
  refine ⟨g, fun h1 ↦ hx1 ((QuotientGroup.eq_one_iff x).mp (by simpa [h1] using hgx.symm)), ?_,
    hgx⟩
  refine mem_bot.mp ((hG.iInf_pLowerCentralSeries_eq_bot hp.out) ▸ mem_iInf.mpr fun k ↦ ?_)
  match k with
  | 0 => exact mem_pLowerCentralSeries_zero p _
  | 1 => exact pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g)
  | k + 2 =>
    set w : G := (seq k).val⁻¹ * g
    have hw1 : w ∈ pLowerCentralSeries p G (k + 1) :=
      QuotientGroup.eq.mp ((hg (k + 1)).trans (hstep_eq k)).symm
    rw [← QuotientGroup.eq_one_iff, show g = (seq k).val * w by simp [w], QuotientGroup.mk_pow,
      hG.mk_mul_pow_pLowerCentralSeries_add_two hpow k (seq k).val
        (pLowerCentralSeries_succ_le k hw1),
      ← QuotientGroup.mk_pow, ← QuotientGroup.mk_pow,
      (QuotientGroup.eq_one_iff _).mpr (seq k).property,
      (QuotientGroup.eq_one_iff _).mpr (pow_mem_pLowerCentralSeries hw1), one_mul]

/-- **Injectivity of `gradedPow` characterizes absence of `p`-torsion** in a profinite powerful
pro-`p` group (no finite generation needed). -/
theorem forall_eq_one_of_pow_eq_one_iff_injective_gradedPow (hG : IsProP p G)
    (hpow : IsPowerful p G) :
    (∀ g : G, g ^ p = 1 → g = 1) ↔ ∀ k, Function.Injective (gradedPow p G k) := by
  refine ⟨fun htors k ↦ ?_, fun hinj g hgp ↦ ?_⟩
  · let f : gradedPiece p G k →+ gradedPiece p G (k + 1) :=
      AddMonoidHom.mk' (gradedPow p G k) (hG.gradedPow_add hpow k)
    refine (injective_iff_map_eq_zero f).mpr fun z hz ↦ ?_
    obtain ⟨a, rfl⟩ := gradedMk_surjective k z
    rw [gradedMk_eq_zero_iff]
    by_contra ha1
    have hH_mem : ∀ j (b : pLowerCentralSeries p G k),
        b ∈ pLowerCentralSeries p (pLowerCentralSeries p G k) j ↔
          (b : G) ∈ pLowerCentralSeries p G (k + j) := fun j b ↦ by
      rw [← hG.map_subtype_pLowerCentralSeries_pLowerCentralSeries hpow k j, mem_map]
      exact ⟨fun hb ↦ ⟨b, hb, rfl⟩, fun ⟨c, hc, hcb⟩ ↦ Subtype.ext hcb ▸ hc⟩
    obtain ⟨h, hne, hhp, -⟩ :=
      (hG.subgroup (pLowerCentralSeries p G k)).exists_pow_eq_one_of_notMem_pLowerCentralSeries_one
        (hG.isPowerful_pLowerCentralSeries hpow k) ((hH_mem 1 a).not.mpr ha1)
        ((hH_mem 2 (a ^ p)).mpr <| by rw [coe_pow]; simpa [f, gradedPow_gradedMk] using hz)
    exact hne (Subtype.ext (htors (h : G) (by rw [← coe_pow, hhp]; rfl)))
  · refine mem_bot.mp ((hG.iInf_pLowerCentralSeries_eq_bot hp.out) ▸ mem_iInf.mpr fun k ↦ ?_)
    induction k with
    | zero => exact mem_pLowerCentralSeries_zero p g
    | succ k ih =>
      exact gradedMk_eq_zero_iff.mp <| hinj k <|
        show gradedPow p G k (gradedMk p G k ⟨g, ih⟩) = gradedPow p G k 0 by
          rw [gradedPow_gradedMk, gradedPow_zero, gradedMk_eq_zero_iff]; simp [hgp]

/-- **Bijectivity of `gradedPow` characterizes absence of `p`-torsion** in a profinite powerful
pro-`p` group (no finite generation needed). -/
theorem forall_eq_one_of_pow_eq_one_iff_bijective_gradedPow (hG : IsProP p G)
    (hpow : IsPowerful p G) :
    (∀ g : G, g ^ p = 1 → g = 1) ↔ ∀ k, Function.Bijective (gradedPow p G k) := by
  rw [hG.forall_eq_one_of_pow_eq_one_iff_injective_gradedPow hpow]
  exact forall_congr' fun k ↦ ⟨fun h ↦ ⟨h, hG.gradedPow_surjective hpow k⟩, fun h ↦ h.1⟩

end IsProP

end ProfiniteProP

end TauCeti
