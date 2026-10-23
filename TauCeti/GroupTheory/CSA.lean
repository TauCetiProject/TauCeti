/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Centralizer
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# CSA groups

A group is CSA if its maximal abelian subgroups are malnormal. The centralizer of a nonidentity
element in such a group is its unique maximal abelian subgroup containing that element. In
particular, commutation is transitive through a nonidentity element. These properties are useful
for the centralizers and equations of free groups and limit groups.

The definition follows Baumslag, Myasnikov and Remeslennikov, *Algebraic geometry over groups I*,
§§1–2.
-/

public section

namespace Group

variable (G : Type*) [Group G]

/-- A group is CSA if each maximal abelian subgroup is malnormal. -/
def IsCSA : Prop :=
  ∀ M : Subgroup G, Maximal (fun K : Subgroup G => IsMulCommutative K) M →
    TauCeti.IsTISubgroup M

/-- Commutation in a group is transitive when the middle element is nonidentity. -/
def IsCommTransitive : Prop :=
  ∀ x y z : G, y ≠ 1 → Commute x y → Commute y z → Commute x z

/-- The defining malnormality condition for a CSA group. -/
theorem isCSA_iff : IsCSA G ↔
    ∀ M : Subgroup G, Maximal (fun K : Subgroup G => IsMulCommutative K) M →
      TauCeti.IsTISubgroup M := Iff.rfl

/-- The defining condition for commutation transitivity. -/
theorem isCommTransitive_iff : IsCommTransitive G ↔
    ∀ x y z : G, y ≠ 1 → Commute x y → Commute y z → Commute x z := Iff.rfl

variable {G}

/-- Every abelian group is CSA. -/
theorem IsCSA.of_commGroup [IsMulCommutative G] : IsCSA G := by
  intro M hM
  have htop : M = ⊤ := by
    apply hM.eq_of_le (by infer_instance : IsMulCommutative (⊤ : Subgroup G))
    exact le_top
  rw [htop]
  exact TauCeti.IsTISubgroup.top

/-- A maximal abelian subgroup in a CSA group is the centralizer of each of its nonidentity
elements. Hence it is the unique maximal abelian subgroup containing such an element. -/
theorem IsCSA.eq_centralizer_of_mem (hG : IsCSA G) {M : Subgroup G}
    (hM : Maximal (fun K : Subgroup G => IsMulCommutative K) M)
    {y : G} (hyM : y ∈ M) (hy : y ≠ 1) :
    M = Subgroup.centralizer {y} := by
  have : IsMulCommutative M := hM.prop
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx hyM)
  · exact (hG M hM).centralizer_singleton_le hyM hy

/-- The centralizer of a nonidentity element in a CSA group is maximal abelian. -/
theorem IsCSA.centralizer_isMaximalAbelian (hG : IsCSA G) {y : G} (hy : y ≠ 1) :
    Maximal (fun K : Subgroup G => IsMulCommutative K) (Subgroup.centralizer {y}) := by
  let H : Subgroup G := Subgroup.closure {y}
  have hH : IsMulCommutative H := by
    apply Subgroup.isMulCommutative_closure
    simp
  obtain ⟨M, hHM, hM⟩ := H.exists_maximal_isMulCommutative hH
  have hyM : y ∈ M := hHM (Subgroup.subset_closure (by simp))
  simpa only [hG.eq_centralizer_of_mem hM hyM hy] using hM

/-- The centralizer of a nonidentity element in a CSA group is abelian. -/
theorem IsCSA.centralizer_isMulCommutative (hG : IsCSA G) {y : G} (hy : y ≠ 1) :
    IsMulCommutative (Subgroup.centralizer {y}) :=
  (hG.centralizer_isMaximalAbelian hy).prop

/-- The centralizer of a nonidentity element in a CSA group is malnormal. -/
theorem IsCSA.centralizer_isTISubgroup (hG : IsCSA G) {y : G} (hy : y ≠ 1) :
    TauCeti.IsTISubgroup (Subgroup.centralizer {y}) :=
  hG _ (hG.centralizer_isMaximalAbelian hy)

/-- Commutation is transitive through a nonidentity element exactly when every nonidentity
element has an abelian centralizer. -/
theorem isCommTransitive_iff_centralizer_isMulCommutative :
    IsCommTransitive G ↔
      ∀ y : G, y ≠ 1 → IsMulCommutative (Subgroup.centralizer {y}) := by
  constructor
  · intro h y hy
    apply IsMulCommutative.of_setLike_mul_comm
    intro a ha b hb
    exact (h a y b hy
      ((commute_iff_eq _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp ha))
      ((commute_iff_eq _ _).mpr (Subgroup.mem_centralizer_singleton_iff.mp hb).symm)).eq
  · intro h x y z hy hxy hyz
    have hx : x ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxy.eq
    have hz : z ∈ Subgroup.centralizer {y} :=
      Subgroup.mem_centralizer_singleton_iff.mpr hyz.eq.symm
    exact (commute_iff_eq _ _).mpr
      ((isMulCommutative_iff_of_setLike.mp (h y hy)) x hx z hz)

/-- CSA groups have transitive commutation through every nonidentity element. -/
theorem IsCSA.isCommTransitive (hG : IsCSA G) : IsCommTransitive G :=
  isCommTransitive_iff_centralizer_isMulCommutative.mpr
    (fun _ hy => hG.centralizer_isMulCommutative hy)

/-- A nonabelian commutative-transitive group has trivial center. -/
theorem IsCommTransitive.center_eq_bot (hG : IsCommTransitive G)
    (h : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  by_contra hz1
  apply h
  exact ⟨⟨fun a b =>
    (hG a z b hz1 (Subgroup.mem_center_iff.mp hz a)
      (Subgroup.mem_center_iff.mp hz b).symm).eq⟩⟩

/-- A nonabelian CSA group has trivial center. -/
theorem IsCSA.center_eq_bot (hG : IsCSA G) (h : ¬ IsMulCommutative G) :
    Subgroup.center G = ⊥ :=
  hG.isCommTransitive.center_eq_bot h

/-- An injective homomorphism into a CSA group has CSA domain. -/
theorem IsCSA.of_injective {H : Type*} [Group H] (hG : IsCSA G)
    (f : H →* G) (hf : Function.Injective f) : IsCSA H := by
  intro M hM
  by_cases hbot : M = ⊥
  · subst M
    exact TauCeti.IsTISubgroup.bot
  · obtain ⟨⟨y, hyM⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
    have hy : y ≠ 1 := fun e => hy1 (Subtype.ext e)
    have hfy : f y ≠ 1 := fun e => hy (hf (by simpa using e))
    let C : Subgroup G := Subgroup.centralizer {f y}
    have hC : Maximal (fun K : Subgroup G => IsMulCommutative K) C :=
      hG.centralizer_isMaximalAbelian hfy
    have : IsMulCommutative C := hC.prop
    have hCM : IsMulCommutative (C.comap f) :=
      C.comap_injective_isMulCommutative hf
    have hMC : M ≤ C.comap f := by
      have : IsMulCommutative M := hM.prop
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr <|
        by simpa only [map_mul] using congrArg f (setLike_mul_comm hx hyM)
    have hM_eq : M = C.comap f := hM.eq_of_le hCM hMC
    rw [hM_eq]
    exact (hG C hC).comap f hf

/-- If `G` is nonabelian and `C` is nontrivial, then `G × C` is not commutative transitive. -/
theorem not_isCommTransitive_prod_of_nontrivial {C : Type*} [Group C]
    [Nontrivial C] (hG : ¬ IsMulCommutative G) :
    ¬ IsCommTransitive (G × C) := by
  intro hprod
  obtain ⟨a, b, hab⟩ : ∃ a b : G, ¬ Commute a b := by
    by_contra h
    push Not at h
    exact hG ⟨⟨h⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : C, c ≠ 1 := exists_ne 1
  have hxy : Commute ((a, 1) : G × C) (1, c) :=
    Commute.prod (Commute.one_right a) (Commute.one_left c)
  have hyz : Commute ((1, c) : G × C) (b, 1) :=
    Commute.prod (Commute.one_left b) (Commute.one_right c)
  have hpair : Commute ((a, 1) : G × C) (b, 1) :=
    hprod _ _ _ (by simpa using hc) hxy hyz
  exact hab (congrArg Prod.fst hpair.eq)

/-- If `G` is nonabelian and `C` is nontrivial, then `G × C` is not CSA. -/
theorem not_isCSA_prod_of_nontrivial {C : Type*} [Group C]
    [Nontrivial C] (hG : ¬ IsMulCommutative G) :
    ¬ IsCSA (G × C) :=
  fun h => (not_isCommTransitive_prod_of_nontrivial hG) h.isCommTransitive

end Group
