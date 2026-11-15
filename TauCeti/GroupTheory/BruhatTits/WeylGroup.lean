/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import TauCeti.GroupTheory.BruhatTits.RootDatum
public import TauCeti.GroupTheory.TitsSystem.Basic
public import TauCeti.LinearAlgebra.RootSystem.Indivisible
import Mathlib.Algebra.Module.Submodule.Union
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.GroupTheory.TitsSystem.Bruhat.Length
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# The Weyl group and Tits system of a Bruhat–Tits root datum

Let `D = (T, (U a, M a))` be a root datum of type `P` in a group `G`, where `P` is a finite
crystallographic root pairing (possibly non-reduced, without assuming `P.IsRootSystem`) over a
linearly ordered field `R`. Each element `n` of `N = D.weylNormalizer` permutes the root subgroups
`D.U a` along a unique element `D.weylGroupHom n` of the Weyl group `P.weylGroup`, sending `T` to
`1` and `M a` to the reflection `s_a`.

Following Bruhat–Tits I, §§6.1.6–6.1.15, we establish:

* changing `D.positiveVector` to any regular coweight `x` preserves all root-datum axioms, in
  particular `(DR6)` (`RootDatum.withPositiveVector`);
* ordering the positive indivisible rays by a separating linear form factors the positive unipotent
  subgroup `U⁺` into ascending root-ray products, yielding the subgroup ray-projection theorem
  (`RootDatum.iSup_inf_U_eq_of_commutator_le`), normalizer triviality in `U⁺`
  (`RootDatum.eq_one_of_mem_positiveSubgroup_of_forall_conj_U`), and `B ∩ N = T`
  (`RootDatum.borelSubgroup_inf_weylNormalizer`);
* `(B, N)` forms a Tits system in `G` when `D` is generating (`RootDatum.IsGenerating.titsSystem`),
  and in `D.generatedSubgroup` in general (`RootDatum.titsSystem`);
* the kernel of `D.weylGroupHom` is `T` (`RootDatum.ker_weylGroupHom`), inducing the canonical
  isomorphism `N / T ≃* W(Φ)` (`RootDatum.weylGroupEquiv`) characterized by
  `n (U a) n⁻¹ = U (ν(n) a)` (`RootDatum.weylGroupEquiv_conj`).

## Main definitions

* `TauCeti.BruhatTits.RootDatum.borelSubgroup`: the subgroup `B = T U⁺`.
* `TauCeti.BruhatTits.RootDatum.generatedSubgroup`: the subgroup `⟨T, U a⟩ ≤ G`.
* `TauCeti.BruhatTits.RootDatum.withPositiveVector`: a root datum with a new regular coweight.
* `TauCeti.BruhatTits.RootDatum.weylGroupHom`: the surjective homomorphism `N →* P.weylGroup`.
* `TauCeti.BruhatTits.RootDatum.IsGenerating.titsSystem`, `RootDatum.titsSystem`: the Tits system
  attached to a root datum.
* `TauCeti.BruhatTits.RootDatum.weylGroupEquiv`: the isomorphism `N / T ≃* P.weylGroup`.

## Main results

* `TauCeti.BruhatTits.RootDatum.reflectionCoset_eq_of_root_eq_two_smul`: `M (2 a) = M a`.
* `TauCeti.BruhatTits.RootDatum.iSup_inf_U_eq_of_commutator_le`: ray projection for
  commutator-closed subgroups of the positive root groups.
* `TauCeti.BruhatTits.RootDatum.borelSubgroup_inf_weylNormalizer`: `B ∩ N = T`.
* `TauCeti.BruhatTits.RootDatum.ker_weylGroupHom`: `ker weylGroupHom = T`.
* `TauCeti.BruhatTits.RootDatum.weylGroupEquiv_conj`, `weylGroupEquiv_reflection`,
  `weylGroupEquiv_torus`, `weylGroupEquiv_reflection_ne_one`: the defining properties of
  `N / T ≃* W(Φ)`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. I*, Publ. Math. IHÉS 41 (1972),
  6.1.2, pp. 108–109, Proposition 6.1.6, p. 111, Proposition 6.1.8, p. 112, 6.1.11, p. 115,
  and Théorème 6.1.15, p. 116.
-/

public section

open scoped Pointwise commutatorElement

namespace TauCeti.BruhatTits.RootDatum

variable {ι R M N : Type*} [Field R] [LinearOrder R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} {G : Type*} [Group G]

/-! ### Helpers on pointwise action, normalizers, and commutators -/

private theorem smul_iSup_subgroup {α : Type*} [Group α] [MulDistribMulAction α G]
    {ι' : Sort*} (a : α) (f : ι' → Subgroup G) :
    a • (⨆ i, f i) = ⨆ i, a • f i :=
  le_antisymm
    (Subgroup.pointwise_smul_subset_iff.mpr <| iSup_le fun i ↦
      Subgroup.pointwise_smul_subset_iff.mp (le_iSup (fun i ↦ a • f i) i))
    (iSup_le fun i ↦ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (le_iSup f i))

private theorem le_biSup_subgroup {ι' : Type*} {p : ι' → Prop} (B : ι' → Subgroup G)
    (i : ι') (hi : p i) : B i ≤ ⨆ (j) (_ : p j), B j :=
  le_iSup₂ (f := fun j (_ : p j) ↦ B j) i hi

private theorem le_normalizer_of_commutator_le₂ {A H : Subgroup G} {ι' : Type*}
    {p : ι' → Prop} {B : ι' → Subgroup G} (hH : H = ⨆ (i) (_ : p i), B i)
    (hcomm : ∀ i, p i → ⁅A, B i⁆ ≤ H) : A ≤ Subgroup.normalizer (H : Set G) := by
  have hBH : ∀ i, p i → B i ≤ H := fun i hi ↦ hH ▸ le_biSup_subgroup B i hi
  have hconj : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H := by
    intro a ha
    let K : Subgroup G := H.comap (MulAut.conj a).toMonoidHom
    suffices H ≤ K from fun h hh ↦ this hh
    rw [hH]
    refine iSup₂_le fun i hi b hb ↦ ?_
    change a * b * a⁻¹ ∈ H
    have heq : a * b * a⁻¹ = ⁅a, b⁆ * b := by group
    rw [heq]
    exact mul_mem (hcomm i hi (Subgroup.commutator_mem_commutator ha hb)) (hBH i hi hb)
  intro a ha
  refine Subgroup.mem_normalizer_iff.mpr fun h ↦ ⟨hconj a ha h, fun hh ↦ ?_⟩
  simpa [mul_assoc] using hconj a⁻¹ (inv_mem ha) (a * h * a⁻¹) hh

/-! ### The Borel subgroup `B = T U⁺` and the generated subgroup `⟨T, U a⟩` -/

section Subgroups

variable (D : RootDatum P G)

/-- The Borel-like subgroup `B = T U⁺` attached to `D.positiveVector`. -/
def borelSubgroup : Subgroup G :=
  D.T ⊔ D.positiveSubgroup

/-- The subgroup of `G` generated by `T` and all root subgroups `U a`. -/
def generatedSubgroup : Subgroup G :=
  D.T ⊔ ⨆ i, D.U i

variable {D}

theorem borelSubgroup_def : D.borelSubgroup = D.T ⊔ D.positiveSubgroup := (rfl)

theorem generatedSubgroup_def : D.generatedSubgroup = D.T ⊔ ⨆ i, D.U i := (rfl)

theorem isGenerating_iff_generatedSubgroup_eq_top : D.IsGenerating ↔ D.generatedSubgroup = ⊤ :=
  D.isGenerating_iff

/-- Induction principle for `D.weylNormalizer`, generated by `D.T` and the reflection cosets
`D.reflectionCoset i`. -/
@[elab_as_elim]
theorem weylNormalizer_induction {motive : D.weylNormalizer → Prop}
    (torus : ∀ t (ht : t ∈ D.T), motive ⟨t, D.T_le_weylNormalizer ht⟩)
    (reflection : ∀ i m (hm : m ∈ D.reflectionCoset i),
      motive ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩)
    (one : motive 1)
    (mul : ∀ x y, motive x → motive y → motive (x * y))
    (inv : ∀ x, motive x → motive x⁻¹) (n : D.weylNormalizer) : motive n := by
  have hmem : (n : G) ∈ Subgroup.closure ((D.T : Set G) ∪ ⋃ i, D.reflectionCoset i) :=
    D.weylNormalizer_def ▸ n.2
  suffices ∀ g, g ∈ Subgroup.closure ((D.T : Set G) ∪ ⋃ i, D.reflectionCoset i) →
      ∀ hg : g ∈ D.weylNormalizer, motive ⟨g, hg⟩ from this n.1 hmem n.2
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro _
    rcases hx with ht | hM
    · exact torus x ht
    · obtain ⟨i, hm⟩ := Set.mem_iUnion.mp hM
      exact reflection i x hm
  | one => exact fun _ ↦ one
  | mul x y hx_cl hy_cl ihx ihy =>
    intro _
    exact mul ⟨x, D.weylNormalizer_def.symm ▸ hx_cl⟩ ⟨y, D.weylNormalizer_def.symm ▸ hy_cl⟩
      (ihx _) (ihy _)
  | inv x hx_cl ih =>
    intro _
    exact inv ⟨x, D.weylNormalizer_def.symm ▸ hx_cl⟩ (ih _)

theorem T_le_borelSubgroup : D.T ≤ D.borelSubgroup := le_sup_left

theorem positiveSubgroup_le_borelSubgroup : D.positiveSubgroup ≤ D.borelSubgroup := le_sup_right

theorem T_le_normalizer_positiveSubgroup :
    D.T ≤ Subgroup.normalizer (D.positiveSubgroup : Set G) := by
  intro t ht
  rw [← Subgroup.conjAct_pointwise_smul_iff, positiveSubgroup_def, smul_iSup_subgroup]
  refine iSup_congr fun i ↦ ?_
  rw [smul_iSup_subgroup]
  exact iSup_congr fun _ ↦ D.conj_smul_U_of_mem_T ht

/-- The carrier of `D.borelSubgroup` is `T * U⁺`. -/
theorem coe_borelSubgroup :
    (D.borelSubgroup : Set G) = (D.T : Set G) * (D.positiveSubgroup : Set G) :=
  Subgroup.coe_mul_of_left_le_normalizer_right D.T D.positiveSubgroup
    D.T_le_normalizer_positiveSubgroup

theorem T_le_generatedSubgroup : D.T ≤ D.generatedSubgroup := le_sup_left

theorem U_le_generatedSubgroup (i : ι) : D.U i ≤ D.generatedSubgroup :=
  le_iSup (fun j ↦ D.U j) i |>.trans le_sup_right

theorem positiveSubgroup_le_generatedSubgroup : D.positiveSubgroup ≤ D.generatedSubgroup :=
  D.positiveSubgroup_le_iff.mpr fun i _ ↦ D.U_le_generatedSubgroup i

theorem borelSubgroup_le_generatedSubgroup : D.borelSubgroup ≤ D.generatedSubgroup :=
  sup_le D.T_le_generatedSubgroup D.positiveSubgroup_le_generatedSubgroup

theorem reflectionCoset_subset_generatedSubgroup (i : ι) :
    D.reflectionCoset i ⊆ D.generatedSubgroup := by
  intro m hm
  obtain ⟨u, hu, _, x, hx, m₁, hm₁, y, hy, rfl⟩ := D.exists_mem_bruhat i
  have hm₁G : m₁ ∈ D.generatedSubgroup := by
    have heq : m₁ = x⁻¹ * (x * m₁ * y) * y⁻¹ := by group
    rw [heq]
    exact mul_mem (mul_mem (D.U_le_generatedSubgroup i (inv_mem hx))
      (D.U_le_generatedSubgroup _ hu)) (D.U_le_generatedSubgroup i (inv_mem hy))
  have hs : m * m₁⁻¹ ∈ D.generatedSubgroup :=
    D.T_le_generatedSubgroup (D.mul_inv_mem_T hm₁ hm)
  simpa [mul_assoc] using mul_mem hs hm₁G

theorem weylNormalizer_le_generatedSubgroup : D.weylNormalizer ≤ D.generatedSubgroup :=
  D.weylNormalizer_le_iff.mpr
    ⟨D.T_le_generatedSubgroup, D.reflectionCoset_subset_generatedSubgroup⟩

theorem borelSubgroup_sup_weylNormalizer [IsStrictOrderedRing R] :
    D.borelSubgroup ⊔ D.weylNormalizer = D.generatedSubgroup := by
  refine le_antisymm
    (sup_le D.borelSubgroup_le_generatedSubgroup D.weylNormalizer_le_generatedSubgroup)
    (sup_le (D.T_le_borelSubgroup.trans le_sup_left) (iSup_le fun i ↦ ?_))
  rcases (D.positiveVector_regular i).lt_or_gt with hi | hi
  · set j := P.reflectionPerm i i
    have hj : 0 < P.root' j D.positiveVector := by
      have : P.root' j D.positiveVector = -P.root' i D.positiveVector := by simp [j]
      linarith
    obtain ⟨m, hm⟩ := D.reflectionCoset_nonempty j
    have hUj : D.U j ≤ D.borelSubgroup :=
      (D.U_le_positiveSubgroup hj).trans D.positiveSubgroup_le_borelSubgroup
    have hmN : m ∈ D.weylNormalizer := D.reflectionCoset_subset_weylNormalizer j hm
    have hconj : D.U i = ConjAct.toConjAct m • D.U j := by
      rw [D.reflection_conjugates j m hm j, P.reflectionPerm_reflectionPerm_self]
    have hB_le : D.borelSubgroup ≤ D.borelSubgroup ⊔ D.weylNormalizer := le_sup_left
    have hN_le : D.weylNormalizer ≤ D.borelSubgroup ⊔ D.weylNormalizer := le_sup_right
    rw [hconj]
    rintro _ ⟨u, hu, rfl⟩
    exact mul_mem (mul_mem (hN_le hmN) (hB_le (hUj hu))) (inv_mem (hN_le hmN))
  · exact ((D.U_le_positiveSubgroup hi).trans D.positiveSubgroup_le_borelSubgroup).trans le_sup_left

private theorem restrictToGenerated_commutator_le (i j : ι)
    (hij : ∀ c : R, 0 < c → P.root j ≠ -(c • P.root i)) :
    ⁅(D.U i).subgroupOf D.generatedSubgroup, (D.U j).subgroupOf D.generatedSubgroup⁆ ≤
      ⨆ (k) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root k = p • P.root i + q • P.root j),
        (D.U k).subgroupOf D.generatedSubgroup := fun g hg ↦ by
  have hg' : (g : G) ∈ ⁅D.U i, D.U j⁆ := by
    have hmap := Subgroup.map_commutator ((D.U i).subgroupOf D.generatedSubgroup)
      ((D.U j).subgroupOf D.generatedSubgroup) D.generatedSubgroup.subtype
    have hsub : ∀ k, Subgroup.map D.generatedSubgroup.subtype
        ((D.U k).subgroupOf D.generatedSubgroup) = D.U k := fun k ↦ by
      simpa using Subgroup.map_subgroupOf_eq_of_le (D.U_le_generatedSubgroup k)
    rw [← hsub i, ← hsub j, ← hmap]
    exact Subgroup.mem_map_of_mem _ hg
  let H : Subgroup D.generatedSubgroup :=
    ⨆ (k) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root k = p • P.root i + q • P.root j),
      (D.U k).subgroupOf D.generatedSubgroup
  have hle : ⨆ (k) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root k = p • P.root i + q • P.root j),
      D.U k ≤ Subgroup.map D.generatedSubgroup.subtype H :=
    iSup₂_le fun k hk x hx ↦ ⟨⟨x, D.U_le_generatedSubgroup k hx⟩,
      Subgroup.mem_iSup_of_mem k (Subgroup.mem_iSup_of_mem hk hx), rfl⟩
  obtain ⟨g₀, hg₀, hval⟩ := hle (D.commutator_le i j hij hg')
  exact (Subtype.ext hval : g₀ = g) ▸ hg₀

variable (D) in
/-- Restricting a root datum `D` in `G` to `D.generatedSubgroup` yields a generating root datum. -/
def restrictToGenerated : RootDatum P D.generatedSubgroup where
  T := D.T.subgroupOf D.generatedSubgroup
  U i := (D.U i).subgroupOf D.generatedSubgroup
  reflectionCoset i := Subtype.val ⁻¹' D.reflectionCoset i
  positiveVector := D.positiveVector
  U_ne_bot i := by
    obtain ⟨⟨u, hu⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (D.U_ne_bot i)
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨⟨u, D.U_le_generatedSubgroup i hu⟩, hu⟩, fun h ↦ hne ?_⟩
    exact Subtype.ext (congrArg (fun x : (D.U i).subgroupOf D.generatedSubgroup ↦
      ((x : D.generatedSubgroup) : G)) h)
  commutator_le := by exact D.restrictToGenerated_commutator_le
  le_of_root_eq_two_smul i j h _ hu := D.le_of_root_eq_two_smul i j h hu
  ne_of_root_eq_two_smul i j h heq := D.ne_of_root_eq_two_smul i j h <| le_antisymm
    (D.le_of_root_eq_two_smul i j h) fun x hx ↦ by
      change (⟨x, D.U_le_generatedSubgroup i hx⟩ : D.generatedSubgroup) ∈
        (D.U j).subgroupOf D.generatedSubgroup
      exact heq ▸ hx
  reflectionCoset_eq i := by
    obtain ⟨m, hm⟩ := D.reflectionCoset_eq i
    have hmM : m ∈ D.reflectionCoset i := by simp [hm, mem_rightCoset_iff]
    refine ⟨⟨m, D.reflectionCoset_subset_generatedSubgroup i hmM⟩, ?_⟩
    ext x; simp [hm, mem_rightCoset_iff, Subgroup.mem_subgroupOf]
  bruhat i x hx := by
    obtain ⟨_, ⟨a, ha, m, hm, rfl⟩, b, hb, hab⟩ :=
      D.bruhat i ⟨hx.1, fun h ↦ hx.2 (Subtype.ext h)⟩
    exact ⟨⟨a * m, mul_mem (D.U_le_generatedSubgroup i ha)
        (D.reflectionCoset_subset_generatedSubgroup i hm)⟩,
      ⟨⟨a, D.U_le_generatedSubgroup i ha⟩, ha,
        ⟨m, D.reflectionCoset_subset_generatedSubgroup i hm⟩, hm, rfl⟩,
      ⟨b, D.U_le_generatedSubgroup i hb⟩, hb, Subtype.ext hab⟩
  reflection_conjugates i m hm j := by
    ext x
    rw [Subgroup.mem_conjAct_smul_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
      ← D.reflection_conjugates i (m : G) hm j, Subgroup.mem_conjAct_smul_iff]
    rfl
  positiveVector_regular := D.positiveVector_regular
  bruhat_separation t ht u hu htu := by
    have hsub : ∀ p : ι → Prop,
        ⨆ (i) (_ : p i), (D.U i).subgroupOf D.generatedSubgroup ≤
          (⨆ (i) (_ : p i), D.U i).subgroupOf D.generatedSubgroup := fun p ↦
      iSup₂_le fun i hi _ hy ↦ Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi hy)
    exact Subtype.ext (D.bruhat_separation t ht u (hsub _ hu) (hsub _ htu))

theorem isGenerating_restrictToGenerated : D.restrictToGenerated.IsGenerating := by
  rw [isGenerating_iff, eq_top_iff]
  intro x _
  let S := D.restrictToGenerated.T ⊔ ⨆ i, D.restrictToGenerated.U i
  have hT : D.restrictToGenerated.T ≤ S := le_sup_left
  have hU : (⨆ i, D.restrictToGenerated.U i) ≤ S := le_sup_right
  have hle : D.generatedSubgroup ≤ Subgroup.map D.generatedSubgroup.subtype S := by
    refine sup_le ?_ (iSup_le fun i y hy ↦ ?_)
    · intro y hy
      exact ⟨⟨y, D.T_le_generatedSubgroup hy⟩, hT hy, rfl⟩
    · exact ⟨⟨y, D.U_le_generatedSubgroup i hy⟩, hU (Subgroup.mem_iSup_of_mem i hy), rfl⟩
  obtain ⟨y, hy, hxy⟩ := hle x.2
  exact (Subtype.ext hxy : y = x) ▸ hy

end Subgroups

/-! ### Finite crystallographic root data -/

section Crystallographic

variable [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] (D : RootDatum P G)

omit [P.IsCrystallographic] in
variable {D} in
/-- Twice a root has the same reflection coset: `M (2 a) = M a` (Bruhat–Tits I, 6.1.2 (9)). -/
theorem reflectionCoset_eq_of_root_eq_two_smul {i j : ι} (h : P.root j = (2 : R) • P.root i) :
    D.reflectionCoset j = D.reflectionCoset i := by
  have hperm : P.reflectionPerm j = P.reflectionPerm i := P.reflectionPerm_eq_of_root_eq_smul h
  have hneg : P.root (P.reflectionPerm j j) = (2 : R) • P.root (P.reflectionPerm i i) := by
    rw [P.root_reflectionPerm, P.reflection_apply_self, P.root_reflectionPerm,
      P.reflection_apply_self, h, smul_neg]
  obtain ⟨u, hu, hne, x, hx, m, hm, y, hy, rfl⟩ := D.exists_mem_bruhat j
  have hui : x * m * y ∈ (D.U (P.reflectionPerm i i) : Set G) \ {1} :=
    ⟨D.le_of_root_eq_two_smul _ _ hneg hu, hne⟩
  have hxi : x⁻¹ ∈ D.U i := D.le_of_root_eq_two_smul i j h (inv_mem hx)
  have hyi : y⁻¹ ∈ D.U i := D.le_of_root_eq_two_smul i j h (inv_mem hy)
  have hmi : m ∈ D.reflectionCoset i := by
    refine D.mem_reflectionCoset_of_mem_mul ?_ ?_ ?_
    · obtain ⟨_, ⟨x', hx', m', hm', rfl⟩, y', hy', hxy'⟩ := D.bruhat i hui
      dsimp only at hxy'
      refine ⟨x⁻¹ * x' * m', ⟨x⁻¹ * x', mul_mem hxi hx', m', hm', rfl⟩, y' * y⁻¹, mul_mem hy' hyi,
        ?_⟩
      dsimp only
      calc (x⁻¹ * x' * m') * (y' * y⁻¹)
          = x⁻¹ * (x' * m' * y') * y⁻¹ := by group
        _ = x⁻¹ * (x * m * y) * y⁻¹ := by rw [hxy']
        _ = m := by group
    · rw [D.reflection_conjugates j m hm i, hperm]
    · rw [D.reflection_conjugates j m hm (P.reflectionPerm i i), hperm, P.reflectionPerm_self]
  ext g
  rw [D.mem_reflectionCoset_iff_mul_inv_mem_T hm, D.mem_reflectionCoset_iff_mul_inv_mem_T hmi]

omit [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
/-- Every element of `P.weylGroup` lifts to an element of `D.weylNormalizer` acting on the root
subgroups along `P.weylGroupToPerm`. -/
theorem exists_mem_weylNormalizer_conj_U (w : P.weylGroup) :
    ∃ n : D.weylNormalizer, ∀ j : ι,
      ConjAct.toConjAct (n : G) • D.U j = D.U (P.weylGroupToPerm w j) := by
  obtain ⟨g, hg⟩ := w
  induction hg using RootPairing.weylGroup.induction with
  | mem i =>
    obtain ⟨m, hm⟩ := D.reflectionCoset_nonempty i
    refine ⟨⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩, fun j ↦ ?_⟩
    rw [D.reflection_conjugates i m hm j]
    rfl
  | one => exact ⟨1, fun j ↦ by simp⟩
  | mul g₁ g₂ hg₁ hg₂ ih₁ ih₂ =>
    obtain ⟨n₁, hn₁⟩ := ih₁
    obtain ⟨n₂, hn₂⟩ := ih₂
    refine ⟨n₁ * n₂, fun j ↦ ?_⟩
    rw [Subgroup.coe_mul, ConjAct.toConjAct_mul, mul_smul, hn₂, hn₁, ← Equiv.Perm.mul_apply,
      ← map_mul]
    rfl

private theorem withPositiveVector_bruhat_separation {x : N} (hx : ∀ i : ι, P.root' i x ≠ 0)
    (t : G) (ht : t ∈ D.T) (u : G) (hu : u ∈ ⨆ (i) (_ : 0 < P.root' i x), D.U i)
    (htu : t * u ∈ ⨆ (i) (_ : P.root' i x < 0), D.U i) : t * u = 1 := by
  obtain ⟨w, hw⟩ := P.exists_weylGroup_root'_pos_iff hx D.positiveVector_regular
  obtain ⟨n, hn⟩ := D.exists_mem_weylNormalizer_conj_U w
  have hneg_iff : ∀ i : ι, P.root' i x < 0 ↔
      P.root' (P.weylGroupToPerm w i) D.positiveVector < 0 := fun i ↦ by
    rcases (hx i).lt_or_gt with hlt | hgt
    · refine ⟨fun _ ↦ ?_, fun _ ↦ hlt⟩
      exact (D.positiveVector_regular (P.weylGroupToPerm w i)).lt_or_gt.resolve_right
        fun h1 ↦ hlt.not_gt ((hw i).mpr h1)
    · exact ⟨fun h ↦ absurd h hgt.not_gt, fun h ↦ absurd ((hw i).mp hgt) h.not_gt⟩
  have ht' : (n : G) * t * (n : G)⁻¹ ∈ D.T :=
    (Subgroup.mem_normalizer_iff.mp (D.weylNormalizer_le_normalizer n.2) t).mp ht
  have hu' : (n : G) * u * (n : G)⁻¹ ∈ D.positiveSubgroup := by
    have hle : ⨆ (i) (_ : 0 < P.root' i x), D.U i ≤
        (ConjAct.toConjAct (n : G))⁻¹ • D.positiveSubgroup := iSup₂_le fun i hi ↦ by
      rw [← Subgroup.pointwise_smul_subset_iff, hn i]
      exact D.U_le_positiveSubgroup ((hw i).mp hi)
    have := hle hu
    rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ConjAct.toConjAct_smul] at this
  have htu' : ((n : G) * t * (n : G)⁻¹) * ((n : G) * u * (n : G)⁻¹) ∈ D.negativeSubgroup := by
    have heq : ((n : G) * t * (n : G)⁻¹) * ((n : G) * u * (n : G)⁻¹) =
        (n : G) * (t * u) * (n : G)⁻¹ := by group
    rw [heq]
    have hle : ⨆ (i) (_ : P.root' i x < 0), D.U i ≤
        (ConjAct.toConjAct (n : G))⁻¹ • D.negativeSubgroup := iSup₂_le fun i hi ↦ by
      rw [← Subgroup.pointwise_smul_subset_iff, hn i]
      exact D.U_le_negativeSubgroup ((hneg_iff i).mp hi)
    have := hle htu
    rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, ConjAct.toConjAct_smul] at this
  have h1 := D.eq_one_of_mul_mem_negativeSubgroup ht' hu' htu'
  calc t * u = (n : G)⁻¹ * (((n : G) * t * (n : G)⁻¹) * ((n : G) * u * (n : G)⁻¹)) * n := by group
    _ = 1 := by rw [h1, mul_one, inv_mul_cancel]

/-- Replacing `D.positiveVector` by any regular coweight `x` yields a root datum with the same
torus, root subgroups, and reflection cosets (Bruhat–Tits I, 6.1.11 (i)). -/
def withPositiveVector (x : N) (hx : ∀ i : ι, P.root' i x ≠ 0) : RootDatum P G where
  T := D.T
  U := D.U
  reflectionCoset := D.reflectionCoset
  positiveVector := x
  U_ne_bot := D.U_ne_bot
  commutator_le := D.commutator_le
  le_of_root_eq_two_smul := D.le_of_root_eq_two_smul
  ne_of_root_eq_two_smul := D.ne_of_root_eq_two_smul
  reflectionCoset_eq := D.reflectionCoset_eq
  bruhat := D.bruhat
  reflection_conjugates := D.reflection_conjugates
  positiveVector_regular := hx
  bruhat_separation := by exact D.withPositiveVector_bruhat_separation hx

@[simp]
theorem withPositiveVector_T (x : N) (hx : ∀ i : ι, P.root' i x ≠ 0) :
    (D.withPositiveVector x hx).T = D.T := (rfl)

@[simp]
theorem withPositiveVector_U (x : N) (hx : ∀ i : ι, P.root' i x ≠ 0) :
    (D.withPositiveVector x hx).U = D.U := (rfl)

@[simp]
theorem withPositiveVector_reflectionCoset (x : N) (hx : ∀ i : ι, P.root' i x ≠ 0) :
    (D.withPositiveVector x hx).reflectionCoset = D.reflectionCoset := (rfl)

@[simp]
theorem withPositiveVector_positiveVector (x : N) (hx : ∀ i : ι, P.root' i x ≠ 0) :
    (D.withPositiveVector x hx).positiveVector = x := (rfl)

omit [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
@[simp]
theorem positiveSubgroup_inf_negativeSubgroup :
    D.positiveSubgroup ⊓ D.negativeSubgroup = ⊥ :=
  eq_bot_iff.mpr fun u ⟨hu₁, hu₂⟩ ↦ by
    simpa using D.eq_one_of_mul_mem_negativeSubgroup D.T.one_mem hu₁ (by simpa using hu₂)

@[simp]
theorem T_inf_positiveSubgroup : D.T ⊓ D.positiveSubgroup = ⊥ := by
  have hreg : ∀ i : ι, P.root' i (-D.positiveVector) ≠ 0 := fun i ↦ by
    simp [D.positiveVector_regular i]
  let D' := D.withPositiveVector (-D.positiveVector) hreg
  refine eq_bot_iff.mpr fun t ⟨ht, hu⟩ ↦ ?_
  have htu : t * 1 ∈ D'.negativeSubgroup := by
    rw [mul_one]
    have hle : D.positiveSubgroup ≤ D'.negativeSubgroup :=
      D.positiveSubgroup_le_iff.mpr fun i hi ↦
        D'.U_le_negativeSubgroup (by simpa [D'] using hi)
    exact hle hu
  simpa using D'.eq_one_of_mul_mem_negativeSubgroup ht D'.positiveSubgroup.one_mem htu

/-! ### The homomorphism `N →* W(Φ)` -/

omit [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] in
private theorem exists_weylGroup_conj_U (n : D.weylNormalizer) :
    ∃ w : P.weylGroup, ∀ j : ι,
      ConjAct.toConjAct (n : G) • D.U j = D.U (P.weylGroupToPerm w j) := by
  induction n using D.weylNormalizer_induction with
  | torus t ht => exact ⟨1, fun j ↦ by simp [D.conj_smul_U_of_mem_T ht]⟩
  | reflection i m hm =>
    refine ⟨RootPairing.weylGroup.ofIdx P i, fun j ↦ ?_⟩
    rw [D.reflection_conjugates i m hm j]
    rfl
  | one => exact ⟨1, fun j ↦ by simp⟩
  | mul n₁ n₂ ih₁ ih₂ =>
    obtain ⟨w₁, hw₁⟩ := ih₁
    obtain ⟨w₂, hw₂⟩ := ih₂
    refine ⟨w₁ * w₂, fun j ↦ ?_⟩
    rw [Subgroup.coe_mul, ConjAct.toConjAct_mul, mul_smul, hw₂, hw₁, ← Equiv.Perm.mul_apply,
      ← map_mul]
  | inv n ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w⁻¹, fun j ↦ ?_⟩
    rw [Subgroup.coe_inv, ConjAct.toConjAct_inv, inv_smul_eq_iff, hw, map_inv, Equiv.Perm.inv_def,
      Equiv.apply_symm_apply]

private theorem weylGroup_eq_one_of_forall_pos {w : P.weylGroup}
    (hw : ∀ a : {i : ι // P.IsIndivisible i},
      0 < P.root' a.1 D.positiveVector →
        0 < P.root' (P.weylGroupToPerm w a.1) D.positiveVector) : w = 1 := by
  let P₀ := P.indivisiblePairing
  let b₀ := P.indivisibleBaseOf D.positiveVector D.positiveVector_regular
  let w₀ := P.indivisibleWeylGroupEquiv.symm w
  have hw₀w : P.indivisibleWeylGroupEquiv w₀ = w :=
    P.indivisibleWeylGroupEquiv.apply_symm_apply w
  have hmaps : Set.MapsTo (P₀.weylGroupToPerm w₀) (TauCeti.posRoots P₀ b₀)
      (TauCeti.posRoots P₀ b₀) := fun a ha ↦ by
    rw [TauCeti.mem_posRoots, P.indivisibleBaseOf_isPos_iff] at ha ⊢
    rw [P.coe_weylGroupToPerm_indivisibleWeylGroupEquiv, hw₀w]
    exact hw a ha
  rw [← hw₀w, TauCeti.eq_one_of_mapsTo_posRoots hmaps, map_one]

private theorem weylGroup_eq_one_of_forall_U_eq {w : P.weylGroup}
    (hw : ∀ j : ι, D.U (P.weylGroupToPerm w j) = D.U j) : w = 1 :=
  D.weylGroup_eq_one_of_forall_pos fun a ha ↦ by
    by_contra hnp
    have hneg : P.root' (P.weylGroupToPerm w a.1) D.positiveVector < 0 :=
      lt_of_le_of_ne (not_lt.mp hnp) (D.positiveVector_regular _)
    have hbot : D.U a.1 ≤ ⊥ := by
      rw [← D.positiveSubgroup_inf_negativeSubgroup]
      exact le_inf (D.U_le_positiveSubgroup ha) (hw a.1 ▸ D.U_le_negativeSubgroup hneg)
    exact D.U_ne_bot a.1 (le_bot_iff.mp hbot)

private theorem weylGroup_unique_of_conj_U {w₁ w₂ : P.weylGroup}
    (h : ∀ j : ι, D.U (P.weylGroupToPerm w₁ j) = D.U (P.weylGroupToPerm w₂ j)) : w₁ = w₂ := by
  rw [← mul_inv_eq_one]
  refine D.weylGroup_eq_one_of_forall_U_eq fun j ↦ ?_
  rw [map_mul, map_inv, Equiv.Perm.mul_apply, h, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

/-- The group homomorphism `N →* P.weylGroup` sending `n ∈ D.weylNormalizer` to the unique Weyl
element `w` such that `n (U a) n⁻¹ = U (w a)` for every root `a`. -/
noncomputable def weylGroupHom : D.weylNormalizer →* P.weylGroup where
  toFun n := (D.exists_weylGroup_conj_U n).choose
  map_one' := by
    refine D.weylGroup_unique_of_conj_U fun j ↦ ?_
    rw [← (D.exists_weylGroup_conj_U 1).choose_spec j]
    simp
  map_mul' n₁ n₂ := by
    refine D.weylGroup_unique_of_conj_U fun j ↦ ?_
    rw [← (D.exists_weylGroup_conj_U (n₁ * n₂)).choose_spec j, Subgroup.coe_mul,
      ConjAct.toConjAct_mul, mul_smul, (D.exists_weylGroup_conj_U n₂).choose_spec j,
      (D.exists_weylGroup_conj_U n₁).choose_spec _, map_mul, Equiv.Perm.mul_apply]

theorem weylGroupHom_conj (n : D.weylNormalizer) (i : ι) :
    ConjAct.toConjAct (n : G) • D.U i = D.U (P.weylGroupToPerm (D.weylGroupHom n) i) :=
  (D.exists_weylGroup_conj_U n).choose_spec i

variable {D} in
theorem eq_weylGroupHom {n : D.weylNormalizer} {w : P.weylGroup}
    (h : ∀ i : ι, ConjAct.toConjAct (n : G) • D.U i = D.U (P.weylGroupToPerm w i)) :
    w = D.weylGroupHom n :=
  D.weylGroup_unique_of_conj_U fun i ↦ (h i).symm.trans (D.weylGroupHom_conj n i)

@[simp]
theorem weylGroupHom_torus {t : G} (ht : t ∈ D.T) :
    D.weylGroupHom ⟨t, D.T_le_weylNormalizer ht⟩ = 1 :=
  (D.eq_weylGroupHom fun i ↦ by simp [D.conj_smul_U_of_mem_T ht]).symm

theorem weylGroupHom_reflection {i : ι} {m : G} (hm : m ∈ D.reflectionCoset i) :
    D.weylGroupHom ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩ =
      RootPairing.weylGroup.ofIdx P i :=
  (D.eq_weylGroupHom fun j ↦ by rw [D.reflection_conjugates i m hm j]; rfl).symm

theorem weylGroupHom_surjective : Function.Surjective D.weylGroupHom := fun w ↦ by
  obtain ⟨n, hn⟩ := D.exists_mem_weylNormalizer_conj_U w
  exact ⟨n, (D.eq_weylGroupHom hn).symm⟩

/-! ### Ordering positive indivisible rays, ray projection, and `B ∩ N = T` -/

/-- A positive indivisible root index of `D`. -/
private abbrev PosIndivisible : Type _ :=
  {a : {i : ι // P.IsIndivisible i} // 0 < P.root' a.1 D.positiveVector}

/-- There exists a coweight `w₀ : N` such that `a ↦ P.root' a w₀ / P.root' a D.positiveVector`
separates all positive indivisible roots. -/
private theorem exists_separating_coweight :
    ∃ w₀ : N, Function.Injective
      (fun a : D.PosIndivisible ↦ P.root' a.1.1 w₀ / P.root' a.1.1 D.positiveVector) := by
  let P₀ := P.indivisiblePairing
  let v := D.positiveVector
  let Pair := {p : D.PosIndivisible × D.PosIndivisible // p.1 ≠ p.2}
  let vec : Pair → M := fun p ↦
    P.root' p.1.2.1.1 v • P.root p.1.1.1.1 - P.root' p.1.1.1.1 v • P.root p.1.2.1.1
  have hvec : ∀ p : Pair, vec p ≠ 0 := by
    rintro ⟨⟨a, b⟩, hab⟩ h0
    have hdep : ¬ LinearIndependent R ![P₀.root a.1, P₀.root b.1] := by
      rw [LinearIndependent.pair_iff]
      push Not
      refine ⟨P.root' b.1.1 v, -P.root' a.1.1 v, ?_, fun hbv ↦ absurd hbv b.2.ne'⟩
      simpa [P₀, vec, neg_smul, sub_eq_add_neg] using h0
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P₀) a.1 b.1 hdep with heq | hneg
    · exact hab (Subtype.ext (P₀.root.injective heq))
    · have hneg' : P.root a.1.1 = -P.root b.1.1 := by simpa [P₀] using hneg
      have : P.root' a.1.1 v = -P.root' b.1.1 v := by simp [RootPairing.root', hneg']
      linarith [a.2, b.2]
  have : Infinite R := Infinite.of_injective (Nat.cast : ℕ → R) Nat.cast_injective
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := R) vec hvec
  refine ⟨P.flip.toPerfPair.symm f, fun a b hq ↦ ?_⟩
  by_contra hab
  refine hf ⟨(a, b), hab⟩ ?_
  have hw_apply : ∀ x : M, f x = P.toLinearMap x (P.flip.toPerfPair.symm f) := fun x ↦ by simp
  rw [hw_apply]
  have hcross : P.root' a.1.1 (P.flip.toPerfPair.symm f) * P.root' b.1.1 v =
      P.root' b.1.1 (P.flip.toPerfPair.symm f) * P.root' a.1.1 v :=
    (div_eq_div_iff a.2.ne' b.2.ne').mp hq
  simp only [vec, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  change P.root' b.1.1 v * P.root' a.1.1 (P.flip.toPerfPair.symm f) -
    P.root' a.1.1 v * P.root' b.1.1 (P.flip.toPerfPair.symm f) = 0
  linarith

/-- Any root positive on `D.positiveVector` is either a positive indivisible root or twice one. -/
private theorem exists_posIndivisible_of_root'_pos {i : ι}
    (hi : 0 < P.root' i D.positiveVector) :
    ∃ a : D.PosIndivisible, i = a.1.1 ∨ P.root i = (2 : R) • P.root a.1.1 := by
  rcases P.isIndivisible_or_exists_root_eq_two_smul i with hind | ⟨j, hj, hij⟩
  · exact ⟨⟨⟨i, hind⟩, hi⟩, .inl rfl⟩
  · have hjpos : 0 < P.root' j D.positiveVector := by
      have : P.root' i D.positiveVector = 2 * P.root' j D.positiveVector := by
        simp [RootPairing.root', hij]
      linarith
    exact ⟨⟨⟨j, hj⟩, hjpos⟩, .inr hij⟩

/-- Given a separating coweight `w₀` and any cut `C : R` avoiding all positive indivisible ratios,
`w₀ - C • D.positiveVector` is regular and makes rays `< C` negative and rays `> C` positive. -/
private theorem root'_sub_smul_ne_zero {w₀ : N} {C : R}
    (hC : ∀ a : D.PosIndivisible, P.root' a.1.1 w₀ / P.root' a.1.1 D.positiveVector ≠ C)
    (i : ι) : P.root' i (w₀ - C • D.positiveVector) ≠ 0 := by
  have hkey : ∀ a : D.PosIndivisible, P.root' a.1.1 (w₀ - C • D.positiveVector) ≠ 0 := fun a h0 ↦ by
    refine hC a ((div_eq_iff a.2.ne').mpr ?_)
    have : P.root' a.1.1 w₀ - C * P.root' a.1.1 D.positiveVector = 0 := by
      simpa [map_sub, map_smul] using h0
    linarith
  rcases (D.positiveVector_regular i).lt_or_gt with hneg | hpos
  · set j := P.reflectionPerm i i
    have hjpos : 0 < P.root' j D.positiveVector := by
      have : P.root' j D.positiveVector = -P.root' i D.positiveVector := by simp [j]
      linarith
    obtain ⟨a, hja | hj2⟩ := D.exists_posIndivisible_of_root'_pos hjpos
    · have : P.root' i (w₀ - C • D.positiveVector) =
          -P.root' a.1.1 (w₀ - C • D.positiveVector) := by
        have hji : i = P.reflectionPerm a.1.1 a.1.1 := by
          rw [← hja]
          exact (P.reflectionPerm_reflectionPerm_self i).symm
        rw [hji]
        simp
      rw [this, neg_ne_zero]
      exact hkey a
    · have hi2 : P.root i = (-2 : R) • P.root a.1.1 := by
        have : P.root i = -P.root j := by simp [j]
        rw [this, hj2, neg_smul]
      have : P.root' i (w₀ - C • D.positiveVector) =
          -2 * P.root' a.1.1 (w₀ - C • D.positiveVector) := by
        simp [RootPairing.root', hi2]
      rw [this]
      exact mul_ne_zero (by norm_num) (hkey a)
  · obtain ⟨a, rfl | hi2⟩ := D.exists_posIndivisible_of_root'_pos hpos
    · exact hkey a
    · have : P.root' i (w₀ - C • D.positiveVector) =
          2 * P.root' a.1.1 (w₀ - C • D.positiveVector) := by
        simp [RootPairing.root', hi2]
      rw [this]
      exact mul_ne_zero two_ne_zero (hkey a)

/-- There exist a coweight `w₀ : N` and an enumeration `Fin (Nat.card D.PosIndivisible) ≃
D.PosIndivisible` along which `P.root' · w₀ / P.root' · D.positiveVector` is strictly increasing. -/
private theorem exists_orderEquiv_posIndivisible :
    ∃ (w₀ : N) (e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible),
      StrictMono (fun k ↦
        P.root' (e k).1.1 w₀ / P.root' (e k).1.1 D.positiveVector) := by
  classical
  obtain ⟨w₀, hq⟩ := D.exists_separating_coweight
  have : Fintype D.PosIndivisible := Fintype.ofFinite _
  let q : D.PosIndivisible → R := fun a ↦ P.root' a.1.1 w₀ / P.root' a.1.1 D.positiveVector
  let s : Finset R := Finset.univ.image q
  have hcard : s.card = Nat.card D.PosIndivisible := by
    rw [Finset.card_image_of_injective _ hq, Finset.card_univ, Fintype.card_eq_nat_card]
  let emb : Fin (Nat.card D.PosIndivisible) ↪o R := s.orderEmbOfFin hcard
  have hmem : ∀ k, ∃ a, q a = emb k := fun k ↦ by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp (Finset.orderEmbOfFin_mem s hcard k)
    exact ⟨a, ha⟩
  have hinj : Function.Injective (fun k ↦ (hmem k).choose) := fun k₁ k₂ hk ↦
    emb.injective ((hmem k₁).choose_spec.symm.trans ((congrArg q hk).trans (hmem k₂).choose_spec))
  have hcard_eq : Fintype.card (Fin (Nat.card D.PosIndivisible)) = Fintype.card D.PosIndivisible :=
    (Fintype.card_fin _).trans Fintype.card_eq_nat_card.symm
  let e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible :=
    Equiv.ofBijective (fun k ↦ (hmem k).choose)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard_eq⟩)
  refine ⟨w₀, e, fun k₁ k₂ hk ↦ ?_⟩
  change q (hmem k₁).choose < q (hmem k₂).choose
  rw [(hmem k₁).choose_spec, (hmem k₂).choose_spec]
  exact emb.strictMono hk

omit [Finite ι] [P.IsCrystallographic] in
/-- Convexity of the separating ratio: if `P.root m = p • α_a + q • α_b` with `p, q > 0` and
`ratio a < ratio b`, then the indivisible root `c` underlying `m` has `ratio a < ratio c < ratio b`.
-/
private theorem ratio_lt_of_root_eq_add {w₀ : N} {a b c : D.PosIndivisible} {m : ι}
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hm : P.root m = p • P.root a.1.1 + q • P.root b.1.1)
    (hc : m = c.1.1 ∨ P.root m = (2 : R) • P.root c.1.1)
    (hab : P.root' a.1.1 w₀ / P.root' a.1.1 D.positiveVector <
      P.root' b.1.1 w₀ / P.root' b.1.1 D.positiveVector) :
    P.root' a.1.1 w₀ / P.root' a.1.1 D.positiveVector <
        P.root' c.1.1 w₀ / P.root' c.1.1 D.positiveVector ∧
      P.root' c.1.1 w₀ / P.root' c.1.1 D.positiveVector <
        P.root' b.1.1 w₀ / P.root' b.1.1 D.positiveVector := by
  let v := D.positiveVector
  have hmc : P.root' m w₀ / P.root' m v = P.root' c.1.1 w₀ / P.root' c.1.1 v := by
    rcases hc with rfl | hc2
    · rfl
    · have h1 : P.root' m w₀ = 2 * P.root' c.1.1 w₀ := by simp [RootPairing.root', hc2]
      have h2 : P.root' m v = 2 * P.root' c.1.1 v := by simp [RootPairing.root', hc2]
      rw [h1, h2, mul_div_mul_left _ _ two_ne_zero]
  rw [← hmc]
  have hm_w : P.root' m w₀ = (p : R) * P.root' a.1.1 w₀ + (q : R) * P.root' b.1.1 w₀ := by
    simp [RootPairing.root', hm, nsmul_eq_mul]
  have hm_v : P.root' m v = (p : R) * P.root' a.1.1 v + (q : R) * P.root' b.1.1 v := by
    simp [RootPairing.root', hm, nsmul_eq_mul]
  have hpR : (0 : R) < p := Nat.cast_pos.mpr hp
  have hqR : (0 : R) < q := Nat.cast_pos.mpr hq
  have hav : 0 < P.root' a.1.1 v := a.2
  have hbv : 0 < P.root' b.1.1 v := b.2
  have hmv : 0 < P.root' m v := by rw [hm_v]; positivity
  have hcross : P.root' a.1.1 w₀ * P.root' b.1.1 v < P.root' b.1.1 w₀ * P.root' a.1.1 v :=
    (div_lt_div_iff₀ hav hbv).mp hab
  constructor
  · rw [div_lt_div_iff₀ hav hmv, hm_w, hm_v]
    nlinarith [mul_lt_mul_of_pos_left hcross hqR]
  · rw [div_lt_div_iff₀ hmv hbv, hm_w, hm_v]
    nlinarith [mul_lt_mul_of_pos_left hcross hpR]

omit [Finite ι] [P.IsCrystallographic] in
/-- Existence of a cut `C` strictly above ray `k` and strictly below all rays `> k`, avoiding all
positive indivisible rays. -/
private theorem exists_cut_after {w₀ : N} {e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible}
    (hmono : StrictMono (fun r : Fin (Nat.card D.PosIndivisible) ↦
      P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector))
    (k : Fin (Nat.card D.PosIndivisible)) :
    ∃ C : R,
      (∀ a : D.PosIndivisible, P.root' a.1.1 w₀ / P.root' a.1.1 D.positiveVector ≠ C) ∧
      P.root' (e k).1.1 w₀ / P.root' (e k).1.1 D.positiveVector < C ∧
      ∀ r : Fin (Nat.card D.PosIndivisible), k.1 + 1 ≤ r.1 →
        C < P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector := by
  let ratio : Fin (Nat.card D.PosIndivisible) → R :=
    fun r ↦ P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector
  by_cases hk1 : k.1 + 1 < Nat.card D.PosIndivisible
  · let k' : Fin (Nat.card D.PosIndivisible) := ⟨k.1 + 1, hk1⟩
    have hlt : ratio k < ratio k' := hmono (Nat.lt_succ_self k.1)
    refine ⟨(ratio k + ratio k') / 2, ?_, by linarith, fun r hr ↦ ?_⟩
    · intro a
      obtain ⟨r, rfl⟩ := e.surjective a
      change ratio r ≠ (ratio k + ratio k') / 2
      rcases lt_or_ge r.1 (k.1 + 1) with hr | hr
      · have hle : ratio r ≤ ratio k := hmono.monotone (Nat.lt_succ_iff.mp hr)
        linarith
      · have hle : ratio k' ≤ ratio r := hmono.monotone hr
        linarith
    · have hle : ratio k' ≤ ratio r := hmono.monotone hr
      linarith
  · refine ⟨ratio k + 1, ?_, by linarith, fun r hr ↦ absurd (hr.trans_lt r.2) hk1⟩
    intro a
    obtain ⟨r, rfl⟩ := e.surjective a
    change ratio r ≠ ratio k + 1
    have hrk : r ≤ k := Nat.le_of_lt_succ (lt_of_lt_of_le r.2 (not_lt.mp hk1))
    have hle : ratio r ≤ ratio k := hmono.monotone hrk
    linarith

/-- Ascending ray filtration `⨆_{r ≥ k} L (e r)` along an enumeration `e` of `D.PosIndivisible`. -/
private def rayFiltration (e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible)
    (L : ι → Subgroup G) (k : ℕ) : Subgroup G :=
  ⨆ (r : Fin (Nat.card D.PosIndivisible)) (_ : k ≤ r.1), L (e r).1.1

/-- Common ascending-ray filtration properties for any commutator-closed family `L i`. -/
private theorem rayFiltration_props {w₀ : N}
    {e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible}
    (hmono : StrictMono (fun r : Fin (Nat.card D.PosIndivisible) ↦
      P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector))
    (L : ι → Subgroup G)
    (hL2 : ∀ i j, 0 < P.root' i D.positiveVector → P.root j = (2 : R) • P.root i → L j ≤ L i)
    (hcomm : ∀ k r : Fin (Nat.card D.PosIndivisible), k < r →
      ⁅L (e k).1.1, L (e r).1.1⁆ ≤
        ⨆ (m) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧
          P.root m = p • P.root (e k).1.1 + q • P.root (e r).1.1), L m) :
    (⨆ (i) (_ : 0 < P.root' i D.positiveVector), L i) = D.rayFiltration e L 0 ∧
      (∀ k : Fin (Nat.card D.PosIndivisible),
        L (e k).1.1 ≤ Subgroup.normalizer (D.rayFiltration e L (k.1 + 1) : Set G)) ∧
      (∀ k : Fin (Nat.card D.PosIndivisible),
        D.rayFiltration e L k.1 = L (e k).1.1 ⊔ D.rayFiltration e L (k.1 + 1)) := by
  let n := Nat.card D.PosIndivisible
  let ratio : Fin n → R := fun r ↦ P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm (iSup₂_le fun i hi ↦ ?_)
      (iSup₂_le fun r _ ↦ le_biSup_subgroup L (e r).1.1 (e r).2)
    obtain ⟨a, rfl | hi2⟩ := D.exists_posIndivisible_of_root'_pos hi
    · obtain ⟨r, hr⟩ := e.surjective a
      exact hr ▸ le_biSup_subgroup (fun r : Fin n ↦ L (e r).1.1) r (Nat.zero_le _)
    · obtain ⟨r, hr⟩ := e.surjective a
      refine (hL2 a.1.1 i a.2 hi2).trans ?_
      exact hr ▸ le_biSup_subgroup (fun r : Fin n ↦ L (e r).1.1) r (Nat.zero_le _)
  · intro k
    refine le_normalizer_of_commutator_le₂ rfl fun r hr ↦
      (hcomm k r hr).trans (iSup₂_le fun m ⟨p, q, hp, hq', hroot⟩ ↦ ?_)
    have hm_pos : 0 < P.root' m D.positiveVector := by
      have : P.root' m D.positiveVector =
          (p : R) * P.root' (e k).1.1 D.positiveVector +
            (q : R) * P.root' (e r).1.1 D.positiveVector := by
        simp [RootPairing.root', hroot, nsmul_eq_mul]
      rw [this]
      have h1 := (e k).2
      have h2 := (e r).2
      positivity
    obtain ⟨c, hc⟩ := D.exists_posIndivisible_of_root'_pos hm_pos
    obtain ⟨s, rfl⟩ := e.surjective c
    have hks : ratio k < ratio s := (D.ratio_lt_of_root_eq_add hp hq' hroot hc (hmono hr)).1
    have hks' : k.1 + 1 ≤ s.1 := hmono.lt_iff_lt.mp hks
    have hLm : L m ≤ L (e s).1.1 := by
      rcases hc with rfl | hc2
      · exact le_rfl
      · exact hL2 (e s).1.1 m (e s).2 hc2
    exact hLm.trans (le_biSup_subgroup (fun r : Fin n ↦ L (e r).1.1) s hks')
  · intro k
    refine le_antisymm (iSup₂_le fun r hr ↦ ?_)
      (sup_le (le_biSup_subgroup (fun r : Fin n ↦ L (e r).1.1) k le_rfl)
        (iSup₂_le fun r hr ↦
          le_biSup_subgroup (fun r : Fin n ↦ L (e r).1.1) r (Nat.le_of_succ_le hr)))
    rcases eq_or_lt_of_le hr with heq | hlt
    · exact Fin.ext heq.symm ▸ le_sup_left
    · exact (le_biSup_subgroup (fun r : Fin n ↦ L (e r).1.1) r hlt).trans le_sup_right

private theorem U_inf_rayFiltration_eq_bot {w₀ : N}
    {e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible}
    (hmono : StrictMono (fun r : Fin (Nat.card D.PosIndivisible) ↦
      P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector))
    (k : Fin (Nat.card D.PosIndivisible)) :
    D.U (e k).1.1 ⊓ D.rayFiltration e D.U (k.1 + 1) = ⊥ := by
  obtain ⟨C, hC, hkC, hrC⟩ := D.exists_cut_after hmono k
  let DC := D.withPositiveVector (w₀ - C • D.positiveVector) (D.root'_sub_smul_ne_zero hC)
  have hUk : D.U (e k).1.1 ≤ DC.negativeSubgroup := DC.U_le_negativeSubgroup <| by
    have hlt := (div_lt_iff₀ (e k).2).mp hkC
    change P.root' (e k).1.1 (w₀ - C • D.positiveVector) < 0
    simpa [map_sub, map_smul] using sub_neg.mpr hlt
  have hUrem : D.rayFiltration e D.U (k.1 + 1) ≤ DC.positiveSubgroup :=
    iSup₂_le fun r hr ↦ DC.U_le_positiveSubgroup <| by
      have hgt := (lt_div_iff₀ (e r).2).mp (hrC r hr)
      change 0 < P.root' (e r).1.1 (w₀ - C • D.positiveVector)
      simpa [map_sub, map_smul] using sub_pos.mpr hgt
  exact eq_bot_iff.mpr ((inf_le_inf hUk hUrem).trans
    (by rw [inf_comm, DC.positiveSubgroup_inf_negativeSubgroup]))

/-- **Ray projection in the positive unipotent subgroup.** Suppose a family of subgroups
`L i ≤ D.U i` indexed by the roots positive on a regular coweight `z` satisfies `(DR2)`-style
commutator closure and `L (2 a) ≤ L a` whenever `2 a` is a root. Then the subgroup generated by all
`L i` (`0 < P.root' i z`) meets each positive indivisible root subgroup `D.U i₀` in `L i₀`. -/
theorem iSup_inf_U_eq_of_commutator_le {z : N} (hz : ∀ i : ι, P.root' i z ≠ 0)
    (L : ι → Subgroup G)
    (hLU : ∀ i, 0 < P.root' i z → L i ≤ D.U i)
    (hL2 : ∀ i j, 0 < P.root' i z → P.root j = (2 : R) • P.root i → L j ≤ L i)
    (hcomm : ∀ i j, 0 < P.root' i z → 0 < P.root' j z →
      ⁅L i, L j⁆ ≤
        ⨆ (k) (_ : ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ P.root k = p • P.root i + q • P.root j), L k)
    {i₀ : ι} (hi₀_ind : P.IsIndivisible i₀) (hi₀_pos : 0 < P.root' i₀ z) :
    (⨆ (i) (_ : 0 < P.root' i z), L i) ⊓ D.U i₀ = L i₀ := by
  let D' := D.withPositiveVector z hz
  change (⨆ (i) (_ : 0 < P.root' i D'.positiveVector), L i) ⊓ D'.U i₀ = L i₀
  obtain ⟨w₀, e, hmono⟩ := D'.exists_orderEquiv_posIndivisible
  let n := Nat.card D'.PosIndivisible
  have hLFrom_le_UFrom : ∀ k, D'.rayFiltration e L k ≤ D'.rayFiltration e D'.U k := fun k ↦
    iSup₂_mono fun r _ ↦ hLU (e r).1.1 (e r).2
  obtain ⟨hiSup_eq, hnorm, hLFrom_split⟩ := D'.rayFiltration_props hmono L hL2
    fun k r _ ↦ hcomm (e k).1.1 (e r).1.1 (e k).2 (e r).2
  obtain ⟨k₀, hk₀⟩ := e.surjective ⟨⟨i₀, hi₀_ind⟩, hi₀_pos⟩
  have hi₀_eq : (e k₀).1.1 = i₀ := congrArg (fun a : D'.PosIndivisible ↦ a.1.1) hk₀
  refine le_antisymm ?_ (le_inf (le_biSup_subgroup L i₀ hi₀_pos) (hLU i₀ hi₀_pos))
  rw [hiSup_eq, ← hi₀_eq]
  intro g ⟨hgL, hgU⟩
  have hstep : ∀ m : ℕ, m ≤ k₀.1 → g ∈ D'.rayFiltration e L m := fun m ↦ by
    induction m with
    | zero => exact fun _ ↦ hgL
    | succ m ih =>
      intro hm
      let km : Fin n := ⟨m, lt_of_lt_of_le (Nat.lt_of_succ_le hm) k₀.2.le⟩
      have hg_m : g ∈ D'.rayFiltration e L km.1 := ih (Nat.le_of_succ_le hm)
      rw [hLFrom_split km, ← SetLike.mem_coe,
        Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hnorm km)] at hg_m
      obtain ⟨x, hx, y, hy, rfl⟩ := hg_m
      have hg_rem : x * y ∈ D'.rayFiltration e D'.U (km.1 + 1) :=
        Subgroup.mem_iSup_of_mem k₀ (Subgroup.mem_iSup_of_mem hm hgU)
      have hx1 : x = 1 := by
        have hx_mem : x ∈ D'.U (e km).1.1 ⊓ D'.rayFiltration e D'.U (km.1 + 1) :=
          ⟨hLU _ (e km).2 hx, (by group : x = (x * y) * y⁻¹) ▸
            mul_mem hg_rem ((D'.rayFiltration e D'.U (km.1 + 1)).inv_mem (hLFrom_le_UFrom _ hy))⟩
        rwa [D'.U_inf_rayFiltration_eq_bot hmono km, Subgroup.mem_bot] at hx_mem
      simpa [hx1] using hy
  have hg_k₀ : g ∈ D'.rayFiltration e L k₀.1 := hstep k₀.1 le_rfl
  rw [hLFrom_split k₀, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hnorm k₀)] at hg_k₀
  obtain ⟨x, hx, y, hy, rfl⟩ := hg_k₀
  have hy1 : y = 1 := by
    have hy_mem : y ∈ D'.U (e k₀).1.1 ⊓ D'.rayFiltration e D'.U (k₀.1 + 1) :=
      ⟨(by group : y = x⁻¹ * (x * y)) ▸
        mul_mem ((D'.U (e k₀).1.1).inv_mem (hLU _ (e k₀).2 hx)) hgU, hLFrom_le_UFrom _ hy⟩
    rwa [D'.U_inf_rayFiltration_eq_bot hmono k₀, Subgroup.mem_bot] at hy_mem
  simpa [hy1] using hx

omit [Finite ι] [P.IsCrystallographic] in
/-- An element of `U (-a)` (with `a` positive) that normalizes `U⁺` is trivial. -/
private theorem eq_one_of_mem_U_neg_of_mem_normalizer_positiveSubgroup {i : ι}
    (hi : 0 < P.root' i D.positiveVector) {x : G} (hx : x ∈ D.U (P.reflectionPerm i i))
    (hn : x ∈ Subgroup.normalizer (D.positiveSubgroup : Set G)) : x = 1 := by
  by_contra hne
  obtain ⟨_, ⟨a, ha, m, hm, rfl⟩, b, hb, hab⟩ := D.bruhat i ⟨hx, hne⟩
  have haP : a ∈ D.positiveSubgroup := D.U_le_positiveSubgroup hi ha
  have hbP : b ∈ D.positiveSubgroup := D.U_le_positiveSubgroup hi hb
  have hm_norm : m ∈ Subgroup.normalizer (D.positiveSubgroup : Set G) := by
    have heq : m = a⁻¹ * x * b⁻¹ := by rw [← hab]; group
    rw [heq]
    exact mul_mem (mul_mem (Subgroup.le_normalizer (inv_mem haP)) hn)
      (Subgroup.le_normalizer (inv_mem hbP))
  obtain ⟨⟨y, hy⟩, hy_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (D.U_ne_bot i)
  have hy_pos : m * y * m⁻¹ ∈ D.positiveSubgroup :=
    (Subgroup.mem_normalizer_iff.mp hm_norm y).mp (D.U_le_positiveSubgroup hi hy)
  have hy_neg : m * y * m⁻¹ ∈ D.negativeSubgroup := by
    refine D.U_le_negativeSubgroup ?_ (D.mul_mul_inv_mem_U_neg_of_mem_reflectionCoset hm hy)
    have : P.root' (P.reflectionPerm i i) D.positiveVector = -P.root' i D.positiveVector := by simp
    linarith
  have h1 : m * y * m⁻¹ = 1 := by
    have : m * y * m⁻¹ ∈ D.positiveSubgroup ⊓ D.negativeSubgroup := ⟨hy_pos, hy_neg⟩
    rwa [D.positiveSubgroup_inf_negativeSubgroup, Subgroup.mem_bot] at this
  refine hy_ne (Subtype.ext ?_)
  dsimp only
  calc y = m⁻¹ * (m * y * m⁻¹) * m := by group
    _ = 1 := by rw [h1]; group

private theorem mem_rayFiltration_succ_of_forall_conj_U {w₀ : N}
    {e : Fin (Nat.card D.PosIndivisible) ≃ D.PosIndivisible}
    (hmono : StrictMono (fun r : Fin (Nat.card D.PosIndivisible) ↦
      P.root' (e r).1.1 w₀ / P.root' (e r).1.1 D.positiveVector))
    (hnorm : ∀ k : Fin (Nat.card D.PosIndivisible),
      D.U (e k).1.1 ≤ Subgroup.normalizer (D.rayFiltration e D.U (k.1 + 1) : Set G))
    (hsplit : ∀ k : Fin (Nat.card D.PosIndivisible),
      D.rayFiltration e D.U k.1 = D.U (e k).1.1 ⊔ D.rayFiltration e D.U (k.1 + 1))
    {u : G} (hn : ∀ j : ι, ConjAct.toConjAct u • D.U j = D.U j)
    (km : Fin (Nat.card D.PosIndivisible)) (hu_m : u ∈ D.rayFiltration e D.U km.1) :
    u ∈ D.rayFiltration e D.U (km.1 + 1) := by
  rw [hsplit km, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hnorm km)] at hu_m
  obtain ⟨x, hx, y, hy, hxy⟩ := hu_m
  obtain ⟨C, hC, hkC, hrC⟩ := D.exists_cut_after hmono km
  let DC := D.withPositiveVector (w₀ - C • D.positiveVector) (D.root'_sub_smul_ne_zero hC)
  set ik := P.reflectionPerm (e km).1.1 (e km).1.1
  have hik_pos : 0 < P.root' ik DC.positiveVector := by
    have hlt := (div_lt_iff₀ (e km).2).mp hkC
    have heq : P.root' ik DC.positiveVector =
        -(P.root' (e km).1.1 w₀ - C * P.root' (e km).1.1 D.positiveVector) := by simp [ik, DC]
    linarith
  have hx_neg : x ∈ DC.U (P.reflectionPerm ik ik) := by
    rw [P.reflectionPerm_reflectionPerm_self]; exact hx
  have hy_pos : y ∈ DC.positiveSubgroup :=
    (iSup₂_le fun r hr ↦ DC.U_le_positiveSubgroup <| by
      have hgt := (lt_div_iff₀ (e r).2).mp (hrC r hr)
      change 0 < P.root' (e r).1.1 (w₀ - C • D.positiveVector)
      simpa [map_sub, map_smul] using sub_pos.mpr hgt) hy
  have hu_norm : u ∈ Subgroup.normalizer (DC.positiveSubgroup : Set G) := by
    rw [← Subgroup.conjAct_pointwise_smul_iff, positiveSubgroup_def, smul_iSup_subgroup]
    exact iSup_congr fun j ↦ by rw [smul_iSup_subgroup]; exact iSup_congr fun _ ↦ hn j
  have hx_norm : x ∈ Subgroup.normalizer (DC.positiveSubgroup : Set G) := by
    have heq : x = u * y⁻¹ := by dsimp only at hxy; rw [← hxy]; group
    exact heq ▸ mul_mem hu_norm (Subgroup.le_normalizer (inv_mem hy_pos))
  have hx1 : x = 1 := DC.eq_one_of_mem_U_neg_of_mem_normalizer_positiveSubgroup hik_pos hx_neg
    hx_norm
  dsimp only at hxy
  simpa [← hxy, hx1] using hy

/-- Any element of `D.positiveSubgroup` that normalizes every root subgroup is trivial
(Bruhat–Tits I, 6.1.2 (10)). -/
theorem eq_one_of_mem_positiveSubgroup_of_forall_conj_U {u : G}
    (hu : u ∈ D.positiveSubgroup)
    (hn : ∀ j : ι, ConjAct.toConjAct u • D.U j = D.U j) : u = 1 := by
  obtain ⟨w₀, e, hmono⟩ := D.exists_orderEquiv_posIndivisible
  let n := Nat.card D.PosIndivisible
  obtain ⟨hpos_eq, hnorm, hUFrom_split⟩ := D.rayFiltration_props hmono D.U
    (fun i j _ ↦ D.le_of_root_eq_two_smul i j) fun k r _ ↦ D.commutator_le _ _ fun c hc hneg ↦ by
      have : P.root' (e r).1.1 D.positiveVector = -c * P.root' (e k).1.1 D.positiveVector := by
        simp [RootPairing.root', hneg]
      nlinarith [(e k).2, (e r).2]
  have hstep : ∀ m : ℕ, m ≤ n → u ∈ D.rayFiltration e D.U m := fun m ↦ by
    induction m with
    | zero => rw [← positiveSubgroup_def] at hpos_eq; exact fun _ ↦ hpos_eq ▸ hu
    | succ m ih =>
      exact fun hm ↦ D.mem_rayFiltration_succ_of_forall_conj_U hmono hnorm hUFrom_split hn
        ⟨m, hm⟩ (ih (Nat.le_of_succ_le hm))
  have hu_n : u ∈ D.rayFiltration e D.U n := hstep n le_rfl
  have hUFrom_n : D.rayFiltration e D.U n = ⊥ :=
    eq_bot_iff.mpr (iSup₂_le fun r hr ↦ absurd (hr.trans_lt r.2) (lt_irrefl n))
  rwa [hUFrom_n, Subgroup.mem_bot] at hu_n

/-- The Borel subgroup meets `D.weylNormalizer` in `D.T` (Bruhat–Tits I, 6.1.11 (ii)). -/
@[simp]
theorem borelSubgroup_inf_weylNormalizer : D.borelSubgroup ⊓ D.weylNormalizer = D.T := by
  refine le_antisymm ?_ (le_inf D.T_le_borelSubgroup D.T_le_weylNormalizer)
  intro g hg
  obtain ⟨hgB, hgN⟩ := Subgroup.mem_inf.mp hg
  have hgB' : g ∈ (D.borelSubgroup : Set G) := hgB
  rw [D.coe_borelSubgroup] at hgB'
  obtain ⟨t, ht, u, hu, rfl⟩ := hgB'
  have huN : u ∈ D.weylNormalizer := by
    have : u = t⁻¹ * (t * u) := by group
    rw [this]
    exact mul_mem (D.T_le_weylNormalizer (inv_mem ht)) hgN
  let nu : D.weylNormalizer := ⟨u, huN⟩
  have hw1 : D.weylGroupHom nu = 1 :=
    D.weylGroup_eq_one_of_forall_pos fun a ha ↦ by
      by_contra hnp
      have hneg : P.root' (P.weylGroupToPerm (D.weylGroupHom nu) a.1) D.positiveVector < 0 :=
        lt_of_le_of_ne (not_lt.mp hnp) (D.positiveVector_regular _)
      have hpos_conj : ConjAct.toConjAct u • D.positiveSubgroup = D.positiveSubgroup :=
        Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hu)
      have hbot : D.U (P.weylGroupToPerm (D.weylGroupHom nu) a.1) ≤ ⊥ := by
        rw [← D.positiveSubgroup_inf_negativeSubgroup]
        refine le_inf ?_ (D.U_le_negativeSubgroup hneg)
        rw [← D.weylGroupHom_conj nu a.1, ← hpos_conj]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (D.U_le_positiveSubgroup ha)
      exact D.U_ne_bot _ (le_bot_iff.mp hbot)
  have hu1 : u = 1 := D.eq_one_of_mem_positiveSubgroup_of_forall_conj_U hu fun j ↦ by
    have := D.weylGroupHom_conj nu j
    rwa [hw1, map_one, Equiv.Perm.one_apply] at this
  simpa [hu1] using ht

theorem subgroupOf_borelSubgroup_weylNormalizer :
    D.borelSubgroup.subgroupOf D.weylNormalizer = D.T.subgroupOf D.weylNormalizer := by
  ext n
  simp only [Subgroup.mem_subgroupOf]
  exact ⟨fun hB ↦ D.borelSubgroup_inf_weylNormalizer ▸ ⟨hB, n.2⟩,
    fun hT ↦ D.T_le_borelSubgroup hT⟩

/-! ### Rank-one Bruhat cell multiplication and Tits system -/

private abbrev posComplement (a : {i : ι // P.IsIndivisible i}) : Subgroup G :=
  ⨆ (c : {i : ι // P.IsIndivisible i})
    (_ : c ∈ TauCeti.posRoots P.indivisiblePairing
      (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular) \ {a}), D.U c.1

private theorem U_le_normalizer_posComplement {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support) :
    D.U a.1 ≤ Subgroup.normalizer (D.posComplement a : Set G) := by
  let P₀ := P.indivisiblePairing
  let b₀ := P.indivisibleBaseOf D.positiveVector D.positiveVector_regular
  have ha_pos : 0 < P.root' a.1 D.positiveVector := P.root'_pos_of_mem_indivisibleBaseOf ha
  refine le_normalizer_of_commutator_le₂ rfl fun c hc ↦ ?_
  have hc_pos : 0 < P.root' c.1 D.positiveVector :=
    (P.indivisibleBaseOf_isPos_iff D.positiveVector_regular c).mp
      ((TauCeti.mem_posRoots P₀ b₀ c).mp hc.1)
  have hnot_opp : ∀ t : R, 0 < t → P.root c.1 ≠ -(t • P.root a.1) := fun t _ hneg ↦ by
    have : P.root' c.1 D.positiveVector = -t * P.root' a.1 D.positiveVector := by
      simp [RootPairing.root', hneg]
    nlinarith
  refine (D.commutator_le a.1 c.1 hnot_opp).trans (iSup₂_le fun k ⟨p, q, hp, hq, hroot⟩ ↦ ?_)
  have hk_pos : 0 < P.root' k D.positiveVector := by
    have : P.root' k D.positiveVector =
        (p : R) * P.root' a.1 D.positiveVector + (q : R) * P.root' c.1 D.positiveVector := by
      simp [RootPairing.root', hroot, nsmul_eq_mul]
    rw [this]; positivity
  obtain ⟨d, hd⟩ := D.exists_posIndivisible_of_root'_pos hk_pos
  have hd_pos : d.1 ∈ TauCeti.posRoots P₀ b₀ :=
    (TauCeti.mem_posRoots P₀ b₀ d.1).mpr
      ((P.indivisibleBaseOf_isPos_iff D.positiveVector_regular d.1).mpr d.2)
  have hd_ne : d.1 ≠ a := fun hda ↦ by
    obtain ⟨r, hr⟩ : ∃ r : R, P.root k = r • P.root a.1 := by
      have hda' : d.1.1 = a.1 := congrArg Subtype.val hda
      exact hd.elim (fun hk ↦ ⟨1, by rw [hk, hda', one_smul]⟩)
        (fun hk2 ↦ ⟨2, by rw [hk2, hda']⟩)
    have hdep : ¬ LinearIndependent R ![P₀.root a, P₀.root c] := by
      rw [LinearIndependent.pair_iff]; push Not; simp only [P₀, P.indivisiblePairing_root]
      refine ⟨(p : R) - r, q, ?_, fun _ ↦ Nat.cast_ne_zero.mpr hq.ne'⟩
      calc ((p : R) - r) • P.root a.1 + (q : R) • P.root c.1
          = ((p : R) • P.root a.1 + (q : R) • P.root c.1) - r • P.root a.1 := by module
        _ = P.root k - P.root k := by
            rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← hroot, ← hr]
        _ = 0 := sub_self _
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P₀) a c hdep with hac | hac
    · exact hc.2 (P₀.root.injective hac).symm
    · have : P.root' a.1 D.positiveVector = -P.root' c.1 D.positiveVector := by
        have hac' : P.root a.1 = -P.root c.1 := by simpa [P₀] using hac
        simp [RootPairing.root', hac']
      linarith
  have hUk : D.U k ≤ D.U d.1.1 :=
    hd.elim (fun hk ↦ hk ▸ le_rfl) (D.le_of_root_eq_two_smul d.1.1 k)
  exact hUk.trans (le_biSup_subgroup (fun x ↦ D.U x.1) d.1 ⟨hd_pos, hd_ne⟩)

private theorem conj_posComplement_eq_self {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support)
    {m : G} (hm : m ∈ D.reflectionCoset a.1) :
    ConjAct.toConjAct m • D.posComplement a = D.posComplement a := by
  let P₀ := P.indivisiblePairing
  have hbij := TauCeti.bijOn_reflectionPerm_posRoots_diff_singleton P₀
    (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular) ha
  have hm_le : ∀ {m' : G}, m' ∈ D.reflectionCoset a.1 →
      ConjAct.toConjAct m' • D.posComplement a ≤ D.posComplement a := fun {m'} hm' ↦ by
    rw [posComplement, smul_iSup_subgroup]
    refine iSup_le fun c ↦ ?_
    rw [smul_iSup_subgroup]
    refine iSup_le fun hc ↦ ?_
    rw [D.reflection_conjugates a.1 m' hm' c.1, ← P.coe_indivisiblePairing_reflectionPerm a c]
    exact le_biSup_subgroup (fun d ↦ D.U d.1) (P₀.reflectionPerm a c) (hbij.mapsTo hc)
  have hm_inv : m⁻¹ ∈ D.reflectionCoset a.1 := by
    simpa [D.reflectionCoset_reflectionPerm_self] using D.inv_mem_reflectionCoset hm
  exact le_antisymm (hm_le hm) (Subgroup.subset_pointwise_smul_iff.mpr <| by
    rw [← ConjAct.toConjAct_inv]; exact hm_le hm_inv)

/-- Decomposition `B = (T ⊔ U_{Φ₀⁺ \ {a}}) * U_a` for a simple indivisible root `a`, together with
normalization of the complement `T ⊔ U_{Φ₀⁺ \ {a}}` by `m ∈ M_a`. -/
private theorem exists_borelSubgroup_decomp_of_mem_support
    {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support)
    {m : G} (hm : m ∈ D.reflectionCoset a.1) :
    ∃ Ba : Subgroup G, Ba ≤ D.borelSubgroup ∧
      ConjAct.toConjAct m • Ba = Ba ∧
      (D.borelSubgroup : Set G) = (Ba : Set G) * (D.U a.1 : Set G) := by
  let P₀ := P.indivisiblePairing
  let b₀ := P.indivisibleBaseOf D.positiveVector D.positiveVector_regular
  let Uother := D.posComplement a
  let Ba : Subgroup G := D.T ⊔ Uother
  have hUother_le : Uother ≤ D.positiveSubgroup := iSup₂_le fun c hc ↦
    D.U_le_positiveSubgroup ((P.indivisibleBaseOf_isPos_iff D.positiveVector_regular c).mp
      ((TauCeti.mem_posRoots P₀ b₀ c).mp hc.1))
  have hBa_le : Ba ≤ D.borelSubgroup :=
    sup_le D.T_le_borelSubgroup (hUother_le.trans D.positiveSubgroup_le_borelSubgroup)
  have hm_Ba : ConjAct.toConjAct m • Ba = Ba := by
    change ConjAct.toConjAct m • (D.T ⊔ Uother) = D.T ⊔ Uother
    rw [Subgroup.smul_sup,
      Subgroup.conjAct_pointwise_smul_eq_self (D.reflectionCoset_subset_normalizer a.1 hm),
      D.conj_posComplement_eq_self ha hm]
  have ha_pos : 0 < P.root' a.1 D.positiveVector := P.root'_pos_of_mem_indivisibleBaseOf ha
  have hpos_sup : Uother ⊔ D.U a.1 = D.positiveSubgroup := by
    refine le_antisymm (sup_le hUother_le (D.U_le_positiveSubgroup ha_pos))
      (D.positiveSubgroup_le_iff.mpr fun i hi ↦ ?_)
    obtain ⟨d, hd⟩ := D.exists_posIndivisible_of_root'_pos hi
    have hUd : D.U i ≤ D.U d.1.1 :=
      hd.elim (fun hk ↦ hk ▸ le_rfl) (D.le_of_root_eq_two_smul d.1.1 i)
    by_cases hda : d.1 = a
    · exact hUd.trans (hda ▸ le_sup_right)
    · have hd_pos : d.1 ∈ TauCeti.posRoots P₀ b₀ :=
        (TauCeti.mem_posRoots P₀ b₀ d.1).mpr
          ((P.indivisibleBaseOf_isPos_iff D.positiveVector_regular d.1).mpr d.2)
      exact hUd.trans ((le_biSup_subgroup (fun x ↦ D.U x.1) d.1 ⟨hd_pos, hda⟩).trans le_sup_left)
  have hT_Uother : D.T ≤ Subgroup.normalizer (Uother : Set G) := fun t ht ↦ by
    rw [← Subgroup.conjAct_pointwise_smul_iff]; dsimp only [Uother, posComplement]
    rw [smul_iSup_subgroup]
    exact iSup_congr fun c ↦ by
      rw [smul_iSup_subgroup]; exact iSup_congr fun _ ↦ D.conj_smul_U_of_mem_T ht
  refine ⟨Ba, hBa_le, hm_Ba, ?_⟩
  rw [D.coe_borelSubgroup, ← hpos_sup,
    Subgroup.coe_mul_of_right_le_normalizer_left Uother (D.U a.1)
      (D.U_le_normalizer_posComplement ha),
    ← mul_assoc, ← Subgroup.coe_mul_of_left_le_normalizer_right D.T Uother hT_Uother]

private theorem exists_mem_of_mem_doubleCoset_mul
    {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support)
    {m g : G} (hm : m ∈ D.reflectionCoset a.1) (w : D.weylNormalizer)
    (hg : g ∈ DoubleCoset.doubleCoset m D.borelSubgroup D.borelSubgroup *
      DoubleCoset.doubleCoset (w : G) D.borelSubgroup D.borelSubgroup) :
    ∃ b₁ ∈ D.borelSubgroup, ∃ u ∈ D.U a.1, ∃ b₂ ∈ D.borelSubgroup,
      g = b₁ * m * u * (w : G) * b₂ := by
  obtain ⟨Ba, hBa_le, hm_Ba, hB_eq⟩ := D.exists_borelSubgroup_decomp_of_mem_support ha hm
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hg
  obtain ⟨b₁, hb₁, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx₁
  obtain ⟨b', hb', b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hx₂
  have hbb' : b * b' ∈ (D.borelSubgroup : Set G) := mul_mem hb hb'
  rw [hB_eq] at hbb'
  obtain ⟨ba, hba, u, hu, hbau⟩ := hbb'
  dsimp only at hbau
  have hmba : m * ba * m⁻¹ ∈ D.borelSubgroup := hBa_le <| by
    rw [← hm_Ba, ← ConjAct.toConjAct_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hba
  refine ⟨b₁ * (m * ba * m⁻¹), mul_mem hb₁ hmba, u, hu, b₂, hb₂, ?_⟩
  calc (b₁ * m * b) * (b' * (w : G) * b₂)
      = b₁ * m * (b * b') * (w : G) * b₂ := by group
    _ = b₁ * m * (ba * u) * (w : G) * b₂ := by rw [← hbau]
    _ = (b₁ * (m * ba * m⁻¹)) * m * u * (w : G) * b₂ := by group

private theorem inv_mul_mul_mem_borelSubgroup (w : D.weylNormalizer) {i : ι} {u : G}
    (hu : u ∈ D.U i)
    (hpos : 0 < P.root' (P.weylGroupToPerm (D.weylGroupHom w)⁻¹ i) D.positiveVector) :
    (w : G)⁻¹ * u * (w : G) ∈ D.borelSubgroup := by
  refine D.positiveSubgroup_le_borelSubgroup (D.U_le_positiveSubgroup hpos ?_)
  rw [← map_inv, ← D.weylGroupHom_conj w⁻¹, Subgroup.mem_conjAct_smul_iff]
  have heq : ((w⁻¹ : D.weylNormalizer) : G)⁻¹ * ((w : G)⁻¹ * u * (w : G)) *
      ((w⁻¹ : D.weylNormalizer) : G) = u := by
    simp only [Subgroup.coe_inv]
    group
  rwa [heq]

/-- When `(w⁻¹ a)` is positive, `(B m B)(B w B) ⊆ B (m w) B`. -/
private theorem doubleCoset_mul_subset_of_root'_pos
    {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support)
    {m : G} (hm : m ∈ D.reflectionCoset a.1) (w : D.weylNormalizer)
    (hpos : 0 < P.root' (P.weylGroupToPerm (D.weylGroupHom w)⁻¹ a.1) D.positiveVector) :
    DoubleCoset.doubleCoset m D.borelSubgroup D.borelSubgroup *
        DoubleCoset.doubleCoset (w : G) D.borelSubgroup D.borelSubgroup ⊆
      DoubleCoset.doubleCoset (m * (w : G)) D.borelSubgroup D.borelSubgroup := fun _ hg ↦ by
  obtain ⟨b₁, hb₁, u, hu, b₂, hb₂, rfl⟩ := D.exists_mem_of_mem_doubleCoset_mul ha hm w hg
  exact DoubleCoset.mem_doubleCoset.mpr
    ⟨b₁, hb₁, ((w : G)⁻¹ * u * (w : G)) * b₂,
      mul_mem (D.inv_mul_mul_mem_borelSubgroup w hu hpos) hb₂, by group⟩

/-- Rank-one double-coset multiplication: `(B m B)(B w B) ⊆ B (m w) B ∪ B w B`. -/
private theorem doubleCoset_mul_subset_union
    {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support)
    {m : G} (hm : m ∈ D.reflectionCoset a.1) (w : D.weylNormalizer) :
    DoubleCoset.doubleCoset m D.borelSubgroup D.borelSubgroup *
        DoubleCoset.doubleCoset (w : G) D.borelSubgroup D.borelSubgroup ⊆
      DoubleCoset.doubleCoset (m * (w : G)) D.borelSubgroup D.borelSubgroup ∪
        DoubleCoset.doubleCoset (w : G) D.borelSubgroup D.borelSubgroup := by
  set j := P.weylGroupToPerm (D.weylGroupHom w)⁻¹ a.1
  rcases (D.positiveVector_regular j).lt_or_gt with hneg | hpos
  · intro g hg
    obtain ⟨b₁, hb₁, u, hu, b₂, hb₂, rfl⟩ := D.exists_mem_of_mem_doubleCoset_mul ha hm w hg
    by_cases hu1 : u = 1
    · exact .inl (DoubleCoset.mem_doubleCoset.mpr ⟨b₁, hb₁, b₂, hb₂, by rw [hu1]; group⟩)
    · right
      set na := P.reflectionPerm a.1 a.1
      have hu_bruhat : u ∈ (D.U (P.reflectionPerm na na) : Set G) \ {1} := by
        rw [P.reflectionPerm_reflectionPerm_self]
        exact ⟨hu, hu1⟩
      obtain ⟨_, ⟨x, hx, m', hm', rfl⟩, y, hy, hxy⟩ := D.bruhat na hu_bruhat
      dsimp only at hxy
      rw [D.reflectionCoset_reflectionPerm_self] at hm'
      have hmx : m * x * m⁻¹ ∈ D.borelSubgroup :=
        D.positiveSubgroup_le_borelSubgroup
          (D.U_le_positiveSubgroup (P.root'_pos_of_mem_indivisibleBaseOf ha)
            (D.mul_mul_inv_mem_U_of_mem_reflectionCoset hm hx))
      have hmm' : m * m' ∈ D.borelSubgroup :=
        D.T_le_borelSubgroup (D.mul_mem_T_of_mem_reflectionCoset hm hm')
      have hwy : (w : G)⁻¹ * y * (w : G) ∈ D.borelSubgroup := by
        refine D.inv_mul_mul_mem_borelSubgroup w hy ?_
        have hperm : P.weylGroupToPerm (D.weylGroupHom w)⁻¹ na = P.reflectionPerm j j :=
          P.weylGroupToPerm_neg (D.weylGroupHom w)⁻¹ a.1
        have hnj : P.root' (P.reflectionPerm j j) D.positiveVector = -P.root' j D.positiveVector :=
          by simp
        linarith [hperm ▸ hnj]
      refine DoubleCoset.mem_doubleCoset.mpr
        ⟨b₁ * (m * x * m⁻¹) * (m * m'), mul_mem (mul_mem hb₁ hmx) hmm',
          ((w : G)⁻¹ * y * (w : G)) * b₂, mul_mem hwy hb₂, by rw [← hxy]; group⟩
  · exact (D.doubleCoset_mul_subset_of_root'_pos ha hm w hpos).trans Set.subset_union_left

private instance intersection_borelSubgroup_normal :
    (D.borelSubgroup.subgroupOf D.weylNormalizer).Normal :=
  D.subgroupOf_borelSubgroup_weylNormalizer ▸ D.T_normal_weylNormalizer

private abbrev titsSimple :
    Set (D.weylNormalizer ⧸ D.borelSubgroup.subgroupOf D.weylNormalizer) :=
  {s | ∃ a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support,
    ∃ (m : G) (hm : m ∈ D.reflectionCoset a.1),
      QuotientGroup.mk ⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩ = s}

private theorem closure_titsSimple_coset (a : {i : ι // P.IsIndivisible i}) (m : G)
    (hm : m ∈ D.reflectionCoset a.1) :
    (QuotientGroup.mk ⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩ :
      D.weylNormalizer ⧸ D.borelSubgroup.subgroupOf D.weylNormalizer) ∈
      Subgroup.closure D.titsSimple := by
  let P₀ := P.indivisiblePairing
  let b₀ := P.indivisibleBaseOf D.positiveVector D.positiveVector_regular
  refine b₀.induction_reflect a
    (p := fun a ↦ ∀ (m : G) (hm : m ∈ D.reflectionCoset a.1),
      (QuotientGroup.mk ⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩ :
        D.weylNormalizer ⧸ D.borelSubgroup.subgroupOf D.weylNormalizer) ∈
        Subgroup.closure D.titsSimple) ?_ ?_ ?_ m hm
  · intro c ih m' hm'
    have hmc : m' ∈ D.reflectionCoset c.1 := by
      rwa [P.coe_indivisiblePairing_reflectionPerm c c, D.reflectionCoset_reflectionPerm_self]
        at hm'
    exact ih m' hmc
  · exact fun c hc m' hm' ↦ Subgroup.subset_closure ⟨c, hc, m', hm', rfl⟩
  · intro c d ih hd m' hm'
    obtain ⟨md, hmd⟩ := D.reflectionCoset_nonempty d.1
    obtain ⟨mc, hmc⟩ := D.reflectionCoset_nonempty c.1
    have hconj : md * mc * md⁻¹ ∈ D.reflectionCoset (P₀.reflectionPerm d c).1 := by
      rw [P.coe_indivisiblePairing_reflectionPerm d c]
      exact D.mul_mul_inv_mem_reflectionCoset hmd hmc
    let nd : D.weylNormalizer := ⟨md, D.reflectionCoset_subset_weylNormalizer d.1 hmd⟩
    let nc : D.weylNormalizer := ⟨mc, D.reflectionCoset_subset_weylNormalizer c.1 hmc⟩
    let nm : D.weylNormalizer := ⟨m', D.reflectionCoset_subset_weylNormalizer _ hm'⟩
    have hmk_eq : (QuotientGroup.mk nm :
        D.weylNormalizer ⧸ D.borelSubgroup.subgroupOf D.weylNormalizer) =
        QuotientGroup.mk (nd * nc * nd⁻¹) := by
      rw [QuotientGroup.eq, D.subgroupOf_borelSubgroup_weylNormalizer, Subgroup.mem_subgroupOf]
      exact D.inv_mul_mem_T hm' hconj
    rw [hmk_eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hsd : (QuotientGroup.mk nd : _) ∈ Subgroup.closure D.titsSimple :=
      Subgroup.subset_closure ⟨d, hd, md, hmd, rfl⟩
    exact mul_mem (mul_mem hsd (ih mc hmc)) (inv_mem hsd)

private theorem closure_titsSimple : Subgroup.closure D.titsSimple = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  induction n using D.weylNormalizer_induction with
  | torus t ht =>
    have h1 : (QuotientGroup.mk ⟨t, D.T_le_weylNormalizer ht⟩ :
        D.weylNormalizer ⧸ D.borelSubgroup.subgroupOf D.weylNormalizer) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (D.T_le_borelSubgroup ht)
    exact h1 ▸ one_mem _
  | reflection i m hm =>
    rcases P.isIndivisible_or_exists_root_eq_two_smul i with hi | ⟨j, hj, hij⟩
    · exact D.closure_titsSimple_coset ⟨i, hi⟩ m hm
    · exact D.closure_titsSimple_coset ⟨j, hj⟩ m
        (D.reflectionCoset_eq_of_root_eq_two_smul hij ▸ hm)
  | one => rw [QuotientGroup.mk_one]; exact one_mem _
  | mul x y ihx ihy => rw [QuotientGroup.mk_mul]; exact mul_mem ihx ihy
  | inv x ih => rw [QuotientGroup.mk_inv]; exact inv_mem ih

private theorem exists_conj_not_mem_borelSubgroup
    {a : {i : ι // P.IsIndivisible i}}
    (ha : a ∈ (P.indivisibleBaseOf D.positiveVector D.positiveVector_regular).support)
    {m : G} (hm : m ∈ D.reflectionCoset a.1) :
    ∃ b : D.borelSubgroup, m * (b : G) * m⁻¹ ∉ D.borelSubgroup := by
  obtain ⟨⟨u, hu⟩, hu_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (D.U_ne_bot a.1)
  have ha_pos : 0 < P.root' a.1 D.positiveVector := P.root'_pos_of_mem_indivisibleBaseOf ha
  refine ⟨⟨u, D.positiveSubgroup_le_borelSubgroup (D.U_le_positiveSubgroup ha_pos hu)⟩,
    fun hconj ↦ ?_⟩
  have hconj' : m * u * m⁻¹ ∈ (D.borelSubgroup : Set G) := hconj
  rw [D.coe_borelSubgroup] at hconj'
  obtain ⟨t, ht, v, hv, htv⟩ := hconj'
  dsimp only at htv
  have hneg : m * u * m⁻¹ ∈ D.negativeSubgroup := by
    refine D.U_le_negativeSubgroup ?_ (D.mul_mul_inv_mem_U_neg_of_mem_reflectionCoset hm hu)
    have : P.root' (P.reflectionPerm a.1 a.1) D.positiveVector =
        -P.root' a.1 D.positiveVector := by simp
    linarith
  have hmu1 : m * u * m⁻¹ = 1 :=
    htv.symm.trans (D.eq_one_of_mul_mem_negativeSubgroup ht hv (htv ▸ hneg))
  refine hu_ne (Subtype.ext ?_)
  dsimp only
  calc u = m⁻¹ * (m * u * m⁻¹) * m := by group
    _ = 1 := by rw [hmu1]; group

variable {D} in
/-- **Tits system of a generating root datum** (Bruhat–Tits I, Théorème 6.1.15). -/
noncomputable def IsGenerating.titsSystem (hG : D.IsGenerating) : TitsSystem G where
  subgroupB := D.borelSubgroup
  subgroupN := D.weylNormalizer
  closure_subgroupB_union_subgroupN := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq,
      D.borelSubgroup_sup_weylNormalizer]
    exact D.isGenerating_iff.mp hG
  intersection_normal := D.intersection_borelSubgroup_normal
  simple := D.titsSimple
  closure_simple := D.closure_titsSimple
  exists_simpleRep_mul_self_mem := by
    rintro s ⟨a, _, m, hm, rfl⟩
    exact ⟨⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩, rfl,
      D.T_le_borelSubgroup (D.mul_self_mem_T hm)⟩
  mul_doubleCoset_subset := by
    rintro s ⟨a, ha, m, hm, rfl⟩
    exact ⟨⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩, rfl,
      D.doubleCoset_mul_subset_union ha hm⟩
  exists_conj_not_mem := by
    rintro s ⟨a, ha, m, hm, rfl⟩
    obtain ⟨b, hb⟩ := D.exists_conj_not_mem_borelSubgroup ha hm
    exact ⟨⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩, rfl, b, hb⟩

@[simp]
theorem IsGenerating.titsSystem_subgroupB {D : RootDatum P G} (hG : D.IsGenerating) :
    hG.titsSystem.subgroupB = D.borelSubgroup :=
  (rfl)

@[simp]
theorem IsGenerating.titsSystem_subgroupN {D : RootDatum P G} (hG : D.IsGenerating) :
    hG.titsSystem.subgroupN = D.weylNormalizer :=
  (rfl)

/-- The Tits system attached to any Bruhat–Tits root datum, in `D.generatedSubgroup`. -/
noncomputable def titsSystem : TitsSystem D.generatedSubgroup :=
  D.isGenerating_restrictToGenerated.titsSystem

/-! ### Kernel of `weylGroupHom` and the isomorphism `N / T ≃* W(Φ)` -/

private theorem IsGenerating.ker_weylGroupHom {D : RootDatum P G} (hG : D.IsGenerating) :
    D.weylGroupHom.ker = D.T.subgroupOf D.weylNormalizer := by
  refine le_antisymm ?_ fun n hn ↦ D.weylGroupHom_torus hn
  intro n hn
  let TS := hG.titsSystem
  let nTS : TS.subgroupN := n
  let q : TS.WeylGroup := QuotientGroup.mk (s := TS.intersection) nTS
  suffices hq1 : q = 1 by
    have hB : nTS ∈ TS.intersection := (QuotientGroup.eq_one_iff (N := TS.intersection) nTS).mp hq1
    change n ∈ D.borelSubgroup.subgroupOf D.weylNormalizer at hB
    rwa [D.subgroupOf_borelSubgroup_weylNormalizer] at hB
  by_contra hq_ne
  obtain ⟨l, hl, hlen, hprod⟩ := TS.exists_prod_eq_of_wordLength q
  rcases l with _ | ⟨s, l'⟩
  · exact hq_ne (hprod.symm.trans List.prod_nil)
  · have hs : s ∈ TS.simple := hl s List.mem_cons_self
    have hl' : ∀ x ∈ l', x ∈ TS.simple := fun x hx ↦ hl x (List.mem_cons_of_mem _ hx)
    have hsq : s * q = l'.prod := by
      rw [← hprod, List.prod_cons, TS.simple_mul_simple_cancel_left hs]
    have hlt_len : TS.simpleGenerators.wordLength (s * q) <
        TS.simpleGenerators.wordLength q := by
      rw [hsq]
      exact (TS.wordLength_prod_le hl').trans_lt (by rw [← hlen, List.length_cons]; omega)
    obtain ⟨a, ha, m, hm, hsmk⟩ := id hs
    let r : TS.subgroupN := ⟨m, D.reflectionCoset_subset_weylNormalizer a.1 hm⟩
    have hpos : 0 < P.root' (P.weylGroupToPerm (D.weylGroupHom n)⁻¹ a.1) D.positiveVector := by
      have hn1 : D.weylGroupHom n = 1 := hn
      rw [hn1, inv_one, map_one, Equiv.Perm.one_apply]
      exact P.root'_pos_of_mem_indivisibleBaseOf ha
    have hcell_eq : TS.bruhatCell s * TS.bruhatCell q = TS.bruhatCell (s * q) := by
      refine Set.Subset.antisymm ?_ (TS.subset_bruhatCell_mul_of_mem_simple hs q)
      have hs_eq : s = QuotientGroup.mk (s := TS.intersection) r := hsmk.symm
      have hq_eq : q = QuotientGroup.mk (s := TS.intersection) nTS := rfl
      rw [hs_eq, hq_eq, ← QuotientGroup.mk_mul, TS.bruhatCell_mk, TS.bruhatCell_mk,
        TS.bruhatCell_mk]
      exact D.doubleCoset_mul_subset_of_root'_pos ha hm n hpos
    exact lt_asymm hlt_len ((TS.bruhatCell_mul_eq_iff_wordLength_lt hs q).mp hcell_eq)

/-- The kernel of `D.weylGroupHom` is `D.T` (Bruhat–Tits I, 6.1.11 (ii)). -/
@[simp]
theorem ker_weylGroupHom : D.weylGroupHom.ker = D.T.subgroupOf D.weylNormalizer := by
  refine le_antisymm ?_ fun n hn ↦ D.weylGroupHom_torus hn
  let D' := D.restrictToGenerated
  have hn'_mem : ∀ m : D.weylNormalizer,
      (⟨(m : G), D.weylNormalizer_le_generatedSubgroup m.2⟩ : D.generatedSubgroup) ∈
        D'.weylNormalizer := fun m ↦ by
    induction m using D.weylNormalizer_induction with
    | torus t ht => exact D'.T_le_weylNormalizer ht
    | reflection i m hm => exact D'.reflectionCoset_subset_weylNormalizer i hm
    | one => exact one_mem _
    | mul x₁ x₂ ih₁ ih₂ => exact mul_mem ih₁ ih₂
    | inv x₁ ih₁ => exact inv_mem ih₁
  intro n hn
  let n' : D'.weylNormalizer := ⟨⟨(n : G), D.weylNormalizer_le_generatedSubgroup n.2⟩, hn'_mem n⟩
  have hhom_eq : D'.weylGroupHom n' = D.weylGroupHom n := by
    refine (D'.eq_weylGroupHom fun i ↦ ?_).symm
    ext x
    rw [Subgroup.mem_conjAct_smul_iff]
    change (n' : D.generatedSubgroup)⁻¹ * x * n' ∈ (D.U i).subgroupOf D.generatedSubgroup ↔
      x ∈ (D.U (P.weylGroupToPerm (D.weylGroupHom n) i)).subgroupOf D.generatedSubgroup
    simp only [Subgroup.mem_subgroupOf]
    rw [← D.weylGroupHom_conj n i, Subgroup.mem_conjAct_smul_iff]
    rfl
  have hn'_ker : n' ∈ D'.weylGroupHom.ker := by
    change D'.weylGroupHom n' = 1
    rw [hhom_eq]
    exact hn
  rw [D.isGenerating_restrictToGenerated.ker_weylGroupHom] at hn'_ker
  exact hn'_ker

/-- **The Weyl group isomorphism of a Bruhat–Tits root datum**: `N / T ≃* W(Φ)`
(Bruhat–Tits I, 6.1.11 (ii)). -/
noncomputable def weylGroupEquiv :
    D.weylNormalizer ⧸ D.T.subgroupOf D.weylNormalizer ≃* P.weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq D.ker_weylGroupHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective D.weylGroupHom D.weylGroupHom_surjective)

@[simp]
theorem weylGroupEquiv_mk (n : D.weylNormalizer) :
    D.weylGroupEquiv (QuotientGroup.mk n) = D.weylGroupHom n :=
  (rfl)

/-- Conjugation by `n ∈ N` permutes the root subgroups along `D.weylGroupEquiv`
(Bruhat–Tits I, 6.1.2 (3)). -/
theorem weylGroupEquiv_conj (n : D.weylNormalizer) (i : ι) :
    ConjAct.toConjAct (n : G) • D.U i =
      D.U (P.weylGroupToPerm (D.weylGroupEquiv (QuotientGroup.mk n)) i) :=
  D.weylGroupHom_conj n i

/-- Every element of `M a` maps to the reflection `s_a` under `D.weylGroupEquiv`. -/
theorem weylGroupEquiv_reflection {i : ι} {m : G} (hm : m ∈ D.reflectionCoset i) :
    D.weylGroupEquiv (QuotientGroup.mk ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩) =
      RootPairing.weylGroup.ofIdx P i :=
  D.weylGroupHom_reflection hm

/-- Every element of `T` maps to `1` under `D.weylGroupEquiv`. -/
theorem weylGroupEquiv_torus {t : G} (ht : t ∈ D.T) :
    D.weylGroupEquiv (QuotientGroup.mk ⟨t, D.T_le_weylNormalizer ht⟩) = 1 :=
  D.weylGroupHom_torus ht

/-- No element of a reflection coset `M a` maps to `1` in `P.weylGroup`. -/
theorem weylGroupEquiv_reflection_ne_one {i : ι} {m : G} (hm : m ∈ D.reflectionCoset i) :
    D.weylGroupEquiv (QuotientGroup.mk ⟨m, D.reflectionCoset_subset_weylNormalizer i hm⟩) ≠ 1 := by
  rw [D.weylGroupEquiv_reflection hm]
  exact RootPairing.weylGroup.ofIdx_ne_one P i

end Crystallographic

end TauCeti.BruhatTits.RootDatum
