/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Commutator.Basic
public import TauCeti.Algebra.Group.Subgroup.Centralizer
public import TauCeti.GroupTheory.TrivialIntersection

/-!
# CSA groups

A group is CSA if its maximal abelian subgroups are malnormal. The centralizer of a nonidentity
element in such a group is its unique maximal abelian subgroup containing that element. In
particular, commutation is transitive through a nonidentity element: the centralizer of a
nonidentity element is abelian, every subset of it containing a nonidentity element has the same
centralizer, and every entry of a list of nonidentity elements in which
consecutive entries commute commutes with the product of the list. Also, if `a`, `x`, `y`, `b`
commute in a chain but `a` and `b` do not commute, then `x = 1` or `y = 1`. In a torsion-free
commutative-transitive group roots are unique, no nonidentity element is conjugate to its
inverse, and in the nonabelian case every nonidentity conjugacy class is infinite. In a
torsion-free CSA group, conjugates of nontrivial powers of `u ≠ 1` by elements of different
cosets of the centralizer of `u` do not commute, and on any finite index set powers `c x` of an
element outside that centralizer can be chosen so that `(c x)⁻¹ * h * c x'` avoids the
centralizer for distinct indices when `h = 1` and for all indices when `h` is a prescribed
nonidentity element of a finite set. A group is CSA exactly when it is commutative transitive
and every nonidentity element commuting with one of its conjugates `g * x * g⁻¹` commutes with
`g`. Consequently, given two noncommuting elements `a` and `b`, the
disjunction `x = 1 ∨ y = 1` is equivalent to `x` commuting with `y`, `a * y * a⁻¹` and
`b * y * b⁻¹`. A failure of either condition is witnessed by a nonidentity element together with a
nontrivial commutator, so both conditions pass to any group in which every pair of nonidentity
elements survives under one homomorphism to a CSA group. This is how fully residually free groups
inherit the CSA property from free groups. These properties are useful for the centralizers and
equations of free groups and limit groups.

A nonabelian CSA group has no element of order two ([MR], §6, Remark 7), and in it every
nonidentity element has a conjugate that does not commute with a given nonidentity element. A list
of nonidentity elements of a CSA group in which some two consecutive entries do not commute can be
conjugated entry by entry, keeping its product, into a list in which no two consecutive entries
commute ([VAR-I], Proposition 3 and Lemma 10); this is how solutions of quadratic equations are
moved into general position. Where [VAR-I] conjugates two consecutive entries by a large power of
their product, the first or the second power suffices here, so no big-powers property is needed;
the absence of involutions makes the second power nontrivial.

The definition follows Baumslag, Myasnikov and Remeslennikov, *Algebraic geometry over groups I*,
§§1–2.

## References

* [MR] A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996); §6, Remark 7 of the
  preprint arXiv:math/9507203.
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §2,
  Proposition 3 and Lemma 10.
-/

public section

open scoped commutatorElement

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

/-- The centralizer of an element in a CSA group is malnormal. -/
theorem IsCSA.centralizer_isTISubgroup (hG : IsCSA G) (y : G) :
    TauCeti.IsTISubgroup (Subgroup.centralizer {y}) := by
  by_cases hy : y = 1
  · rw [hy, Subgroup.centralizer_eq_top_iff_subset.2 (by simp)]
    exact TauCeti.IsTISubgroup.top
  · exact hG _ (hG.centralizer_isMaximalAbelian hy)

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

/-- In a commutative-transitive group, elements of the centralizer of `d ≠ 1` commute with each
other. -/
theorem IsCommTransitive.commute_of_mem_centralizer_singleton (hG : IsCommTransitive G)
    {d g h : G} (hd : d ≠ 1) (hg : g ∈ Subgroup.centralizer {d})
    (hh : h ∈ Subgroup.centralizer {d}) : Commute g h :=
  have := isCommTransitive_iff_centralizer_isMulCommutative.1 hG d hd
  setLike_mul_comm hg hh

/-- In a commutative-transitive group, a subset of the centralizer of `d ≠ 1` that contains a
nonidentity element has the same centralizer as `d`. -/
theorem IsCommTransitive.centralizer_eq_centralizer_singleton (hG : IsCommTransitive G)
    {d g : G} {S : Set G} (hd : d ≠ 1) (hS : S ⊆ Subgroup.centralizer {d}) (hgS : g ∈ S)
    (hg : g ≠ 1) : Subgroup.centralizer S = Subgroup.centralizer {d} := by
  refine le_antisymm (fun h hh ↦ Subgroup.mem_centralizer_singleton_iff.2 ?_) fun h hh ↦
    Subgroup.mem_centralizer_iff.2 fun s hs ↦ (hG.commute_of_mem_centralizer_singleton hd (hS hs)
      hh).eq
  exact (isCommTransitive_iff G).1 hG _ _ _ hg (Subgroup.mem_centralizer_iff.1 hh g hgS).symm
    (Subgroup.mem_centralizer_singleton_iff.1 (hS hgS))

/-- In a commutative-transitive group, every entry of a `Commute`-chain of nonidentity elements
commutes with the product of the chain. -/
theorem IsCommTransitive.commute_list_prod_of_isChain (hG : IsCommTransitive G) {l : List G}
    (hl : l.IsChain Commute) (h1 : ∀ g ∈ l, g ≠ 1) {g : G} (hg : g ∈ l) : Commute g l.prod := by
  -- Commutation between nonidentity elements is transitive.
  let R : G → G → Prop := fun a b ↦ Commute a b ∧ a ≠ 1 ∧ b ≠ 1
  have : Trans R R R :=
    ⟨fun hab hbc ↦ ⟨(isCommTransitive_iff G).1 hG _ _ _ hab.2.2 hab.1 hbc.1, hab.2.1, hbc.2.2⟩⟩
  have : Std.Symm (Commute : G → G → Prop) := ⟨fun _ _ h ↦ h.symm⟩
  have hR : l.IsChain R := hl.imp_of_mem_imp fun a b ha hb h ↦ ⟨h, h1 a ha, h1 b hb⟩
  exact Commute.list_prod_right _ _ fun g' hg' ↦
    (hR.pairwise.imp And.left).forall_of_forall (fun g _ ↦ Commute.refl g) hg hg'

/-- CSA groups have transitive commutation through every nonidentity element. -/
theorem IsCSA.isCommTransitive (hG : IsCSA G) : IsCommTransitive G :=
  isCommTransitive_iff_centralizer_isMulCommutative.mpr
    (fun _ hy => hG.centralizer_isMulCommutative hy)

/-- **Elementwise characterization of CSA groups.** A group is CSA exactly when commutation is
transitive through nonidentity elements and every nonidentity element `x` commuting with a
conjugate `g * x * g⁻¹` commutes with `g`. -/
theorem isCSA_iff_isCommTransitive_and_commute_conj :
    IsCSA G ↔ IsCommTransitive G ∧
      ∀ x g : G, x ≠ 1 → Commute x (g * x * g⁻¹) → Commute x g := by
  constructor
  · refine fun hG => ⟨hG.isCommTransitive, fun x g hx hxg => ?_⟩
    -- Both `x` and `g * x * g⁻¹` lie in the malnormal centralizer of `x`, so `g` does too.
    by_contra hg
    exact (hG.centralizer_isTISubgroup x).conj_notMem
      (fun h => hg (Subgroup.mem_centralizer_singleton_iff.1 h).symm)
      (Subgroup.mem_centralizer_singleton_iff.2 rfl) hx
      (Subgroup.mem_centralizer_singleton_iff.2 hxg.eq.symm)
  · rintro ⟨hG, hconj⟩ M hM
    rw [TauCeti.isTISubgroup_iff]
    intro g x hg hxM hgxM
    by_contra hx
    -- A maximal abelian subgroup containing `x ≠ 1` is the abelian centralizer of `x`.
    have : IsMulCommutative M := hM.prop
    have hMC : M = Subgroup.centralizer {x} :=
      hM.eq_of_le (isCommTransitive_iff_centralizer_isMulCommutative.1 hG x hx) fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.2 (setLike_mul_comm hy hxM)
    apply hg
    rw [hMC, Subgroup.mem_centralizer_singleton_iff]
    exact (hconj x g hx ((commute_iff_eq _ _).2 (setLike_mul_comm hxM hgxM))).eq.symm

/-- In a CSA group, if a nonidentity element `x` of the centralizer of `u` commutes with a
conjugate `g * y * g⁻¹` of another nonidentity element `y` of that centralizer, then `g`
centralizes `u`. -/
theorem IsCSA.mem_centralizer_of_commute_conj (hG : IsCSA G) {u x y g : G}
    (hx : x ∈ Subgroup.centralizer {u}) (hx1 : x ≠ 1) (hy : y ∈ Subgroup.centralizer {u})
    (hy1 : y ≠ 1) (h : Commute x (g * y * g⁻¹)) : g ∈ Subgroup.centralizer {u} := by
  rcases eq_or_ne u 1 with rfl | hu
  · exact Subgroup.mem_centralizer_singleton_iff.2 (by simp)
  have hT := hG.isCommTransitive
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy ⊢
  -- Both `y` and its conjugate lie in the malnormal centralizer of `x`, hence so does `g`.
  have hyx : y ∈ Subgroup.centralizer {x} :=
    Subgroup.mem_centralizer_singleton_iff.2 (hT y u x hu hy hx.symm).eq
  have hg : g ∈ Subgroup.centralizer {x} := by
    by_contra hg
    exact (hG.centralizer_isTISubgroup x).conj_notMem hg hyx hy1
      (Subgroup.mem_centralizer_singleton_iff.2 h.eq.symm)
  exact (hT g x u hx1 (Subgroup.mem_centralizer_singleton_iff.1 hg) hx).eq

/-- In a CSA group, an element conjugating `u` into its own centralizer centralizes `u`: if
`g⁻¹ * u * g` commutes with `u`, then so does `g`. -/
theorem IsCSA.mem_centralizer_of_conj_mem_centralizer (hG : IsCSA G) {u g : G}
    (h : g⁻¹ * u * g ∈ Subgroup.centralizer {u}) : g ∈ Subgroup.centralizer {u} := by
  rcases eq_or_ne u 1 with rfl | hu
  · exact Subgroup.mem_centralizer_singleton_iff.2 (by simp)
  have huu : u ∈ Subgroup.centralizer {u} := Subgroup.mem_centralizer_singleton_iff.2 rfl
  refine inv_mem_iff.1 (hG.mem_centralizer_of_commute_conj huu hu huu hu ?_)
  rw [inv_inv, commute_iff_eq]
  exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm

/-- In a torsion-free CSA group, conjugates of nonzero powers of `u` by `y` and `y'` do not
commute unless `y⁻¹ * y'` centralizes `u`. -/
theorem IsCSA.not_commute_conj_zpow (hG : IsCSA G) [IsMulTorsionFree G] {u y y' : G}
    {e e' : ℤ} (he : e ≠ 0) (he' : e' ≠ 0)
    (hy : y⁻¹ * y' ∉ Subgroup.centralizer {u}) :
    ¬Commute (y * u ^ e * y⁻¹) (y' * u ^ e' * y'⁻¹) := by
  intro h
  obtain rfl | hu := eq_or_ne u 1
  · exact hy (Subgroup.mem_centralizer_singleton_iff.2 (by simp))
  have hu' : u ∈ Subgroup.centralizer {u} := Subgroup.mem_centralizer_singleton_iff.2 rfl
  refine hy (hG.mem_centralizer_of_commute_conj (zpow_mem hu' e)
    (fun h => he ((IsMulTorsionFree.zpow_eq_one_iff_right hu).1 h)) (zpow_mem hu' e')
    (fun h => he' ((IsMulTorsionFree.zpow_eq_one_iff_right hu).1 h)) ?_)
  rw [← Commute.conj_iff y]
  convert h using 1
  group

/-- In a CSA group, if some element lies outside the centralizer `C_G(u)` of `u ≠ 1`, then `G` is
not covered by two left cosets `a * C_G(u)` and `b * C_G(u)`; this uses malnormality of
`C_G(u)`. -/
theorem IsCSA.exists_inv_mul_notMem_centralizer (hG : IsCSA G) {u g : G} (hu : u ≠ 1)
    (hg : g ∉ Subgroup.centralizer {u}) (a b : G) :
    ∃ W, a⁻¹ * W ∉ Subgroup.centralizer {u} ∧ b⁻¹ * W ∉ Subgroup.centralizer {u} := by
  have hu' : u ∈ Subgroup.centralizer {u} := Subgroup.mem_centralizer_singleton_iff.2 rfl
  by_cases hd : a⁻¹ * b ∈ Subgroup.centralizer {u}
  · refine ⟨a * g, by simpa using hg, fun h => hg ?_⟩
    simpa [mul_assoc] using mul_mem hd h
  · -- `W = a * u * (a⁻¹ * b)`: then `b⁻¹ * W` is a conjugate of `u` by an element outside
    -- `C_G(u)`.
    refine ⟨a * u * (a⁻¹ * b), fun h => hd ?_, fun h => ?_⟩
    · simpa [mul_assoc] using mul_mem (inv_mem hu') h
    · exact (hG.centralizer_isTISubgroup u).conj_notMem (g := (a⁻¹ * b)⁻¹)
        (fun h' => hd (by simpa using inv_mem h')) hu' hu (by simpa [mul_assoc] using h)

/-- In a torsion-free CSA group, given `v` outside `C_G(u)`, one can choose powers of `v` whose
mixed products `(v ^ n x)⁻¹ * h * v ^ n x'` avoid `C_G(u)` for distinct indices in the finite set
`s` when `h = 1`, and for all indices in `s` when `h` is a prescribed nonidentity element of the
finite set `T`. -/
theorem IsCSA.exists_inv_pow_mul_mul_pow_notMem_centralizer (hG : IsCSA G) [IsMulTorsionFree G]
    {ι : Type*} {u v : G} (hv : v ∉ Subgroup.centralizer {u}) (s : Finset ι)
    (T : Set G) (hT : T.Finite) :
    ∃ n : ι → ℕ, ∀ x ∈ s, ∀ x' ∈ s, ∀ h : G, (h = 1 ∧ x ≠ x' ∨ h ∈ T ∧ h ≠ 1) →
      (v ^ n x)⁻¹ * h * v ^ n x' ∉ Subgroup.centralizer {u} := by
  have hv1 : v ≠ 1 := by rintro rfl; exact hv (Subgroup.one_mem _)
  exact (hG.centralizer_isTISubgroup u).exists_inv_pow_mul_mul_pow_notMem hv
    (not_isOfFinOrder_of_isMulTorsionFree hv1) s T hT

/-- In a CSA group with two noncommuting elements `a` and `b`, an element `x` is trivial or `y`
is trivial exactly when `x` commutes with `y`, `a * y * a⁻¹` and `b * y * b⁻¹`. This expresses
the disjunction `x = 1 ∨ y = 1` by three equations. -/
theorem IsCSA.eq_one_or_eq_one_iff_commute_conj (hG : IsCSA G) {a b x y : G}
    (hab : ¬Commute a b) :
    x = 1 ∨ y = 1 ↔ Commute x y ∧ Commute x (a * y * a⁻¹) ∧ Commute x (b * y * b⁻¹) := by
  refine ⟨by rintro (rfl | rfl) <;> simp, fun ⟨hxy, hxa, hxb⟩ => ?_⟩
  by_contra! h
  obtain ⟨hx, hy⟩ := h
  have hT := hG.isCommTransitive
  have hconj := (isCSA_iff_isCommTransitive_and_commute_conj.1 hG).2
  -- `y` commutes with its conjugates by `a` and by `b` through `x`, hence with `a` and `b`.
  have hya : Commute y a := hconj y a hy (hT y x _ hx hxy.symm hxa)
  have hyb : Commute y b := hconj y b hy (hT y x _ hx hxy.symm hxb)
  exact hab (hT a y b hy hya.symm hyb)

/-- In a commutative-transitive group, if `a` commutes with `x`, `x` with `y` and `y` with `b`,
but `a` and `b` do not commute, then `x = 1` or `y = 1`. -/
theorem IsCommTransitive.eq_one_or_eq_one_of_not_commute (hG : IsCommTransitive G)
    {a b x y : G} (hab : ¬Commute a b) (hax : Commute a x) (hxy : Commute x y)
    (hyb : Commute y b) : x = 1 ∨ y = 1 := by
  by_contra! h
  exact hab (hG a y b h.2 (hG a x y h.1 hax hxy) hyb)

/-- In a torsion-free commutative-transitive group, a nonidentity element is not conjugate to its
inverse. -/
theorem IsCommTransitive.not_isConj_inv [IsMulTorsionFree G] (hG : IsCommTransitive G) {x : G}
    (hx : x ≠ 1) : ¬IsConj x x⁻¹ := by
  rintro h
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  have hxx : x * x ≠ 1 := by
    rw [← pow_two]
    exact (pow_eq_one_iff_left two_ne_zero).not.2 hx
  -- Conjugating twice by `g` fixes `x`, so `g ^ 2` commutes with `x`.
  have hg2 : Commute (g ^ 2) x := by
    have h2 : g * (g * x * g⁻¹) * g⁻¹ = x := by
      calc g * (g * x * g⁻¹) * g⁻¹ = g * x⁻¹ * g⁻¹ := by rw [hg]
        _ = (g * x * g⁻¹)⁻¹ := by group
        _ = x := by rw [hg, inv_inv]
    calc g ^ 2 * x = g * (g * x * g⁻¹) * g⁻¹ * g ^ 2 := by simp [pow_two, mul_assoc]
      _ = x * g ^ 2 := by rw [h2]
  have hgx : Commute g x := by
    by_cases hg1 : g ^ 2 = 1
    · rw [(pow_eq_one_iff_left two_ne_zero).1 hg1]
      exact Commute.one_left x
    · exact hG g (g ^ 2) x hg1 (Commute.self_pow g 2) hg2
  rw [hgx.eq, mul_inv_cancel_right] at hg
  exact hxx (mul_eq_one_iff_eq_inv.2 hg)

/-- A torsion-free commutative-transitive group has unique roots: for all `x` and `y`, if
`x ^ n = y ^ n` with `n ≠ 0`, then `x = y`. -/
theorem IsCommTransitive.hasUniqueRoots [IsMulTorsionFree G] (hG : IsCommTransitive G) :
    HasUniqueRoots G where
  pow_left_injective n hn x y hxy := by
    dsimp only at hxy
    obtain rfl | hy := eq_or_ne y 1
    · rwa [one_pow, pow_eq_one_iff_left hn] at hxy
    -- Both `x` and `y` commute with the nonidentity element `y ^ n`, hence with each other.
    have hyn : y ^ n ≠ 1 := (pow_eq_one_iff_left hn).not.2 hy
    have hcomm : Commute x y :=
      hG x (y ^ n) y hyn (by rw [← hxy]; exact Commute.self_pow x n) (Commute.pow_self y n)
    exact hcomm.eq_of_pow_eq_pow hn hxy

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

/-- In a nonabelian torsion-free commutative-transitive group, every nonidentity element has an
infinite conjugacy class. -/
theorem IsCommTransitive.infinite_setOf_isConj [IsMulTorsionFree G] (hG : IsCommTransitive G)
    (h : ¬ IsMulCommutative G) {g : G} (hg : g ≠ 1) :
    {x : G | IsConj g x}.Infinite := by
  have := hG.hasUniqueRoots
  refine infinite_setOf_isConj_of_notMem_center ?_
  rwa [hG.center_eq_bot h, Subgroup.mem_bot]

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
      exact Subgroup.mem_centralizer_singleton_iff.mpr <| (commute_iff_eq _ _).mpr <|
        by simpa only [map_mul] using congrArg f (setLike_mul_comm hx hyM)
    have hM_eq : M = C.comap f := hM.eq_of_le hCM hMC
    rw [hM_eq]
    exact (hG C hC).comap f hf

/-- Commutation transitivity passes from `H` to `G` when any two nonidentity elements of `G`
survive together under some homomorphism `G →* H`. -/
theorem IsCommTransitive.of_forall_exists_monoidHom {H : Type*} [Group H]
    (hH : IsCommTransitive H)
    (h : ∀ a b : G, a ≠ 1 → b ≠ 1 → ∃ φ : G →* H, φ a ≠ 1 ∧ φ b ≠ 1) :
    IsCommTransitive G := by
  intro x y z hy hxy hyz
  rw [← commutatorElement_eq_one_iff_commute]
  -- Otherwise one homomorphism keeps both `y` and `⁅x, z⁆` nontrivial, contradicting commutation
  -- transitivity in `H`.
  by_contra hxz
  obtain ⟨φ, hφy, hφxz⟩ := h y ⁅x, z⁆ hy hxz
  apply hφxz
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact hH _ _ _ hφy (hxy.map φ) (hyz.map φ)

/-- Being CSA passes from `H` to `G` when any two nonidentity elements of `G` survive together
under some homomorphism `G →* H`. In particular a group discriminated by a CSA group is CSA. -/
theorem IsCSA.of_forall_exists_monoidHom {H : Type*} [Group H] (hH : IsCSA H)
    (h : ∀ a b : G, a ≠ 1 → b ≠ 1 → ∃ φ : G →* H, φ a ≠ 1 ∧ φ b ≠ 1) : IsCSA G := by
  refine isCSA_iff_isCommTransitive_and_commute_conj.2
    ⟨hH.isCommTransitive.of_forall_exists_monoidHom h, fun x g hx hxg => ?_⟩
  rw [← commutatorElement_eq_one_iff_commute]
  -- Otherwise one homomorphism keeps both `x` and `⁅x, g⁆` nontrivial, contradicting the
  -- elementwise characterization of CSA groups in `H`.
  by_contra hxg'
  obtain ⟨φ, hφx, hφxg⟩ := h x ⁅x, g⁆ hx hxg'
  apply hφxg
  rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
  exact (isCSA_iff_isCommTransitive_and_commute_conj.1 hH).2 _ _ hφx (by simpa using hxg.map φ)

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

/-! ### Moving a list of elements into general position by conjugations -/

/-- A nonabelian CSA group has no element of order two ([MR], §6, Remark 7). -/
theorem IsCSA.eq_one_of_sq_eq_one (hG : IsCSA G) (h : ¬IsMulCommutative G) {s : G}
    (hs : s ^ 2 = 1) : s = 1 := by
  have hs' : s * s = 1 := by rw [← sq, hs]
  have hss : ∀ x, s * (s * x) = x := fun x => by rw [← mul_assoc, hs', one_mul]
  rw [← Subgroup.mem_bot, ← hG.center_eq_bot h, Subgroup.mem_center_iff]
  intro g
  -- Conjugation by `s` inverts `p = s * (g * s * g⁻¹)`, so `s` centralizes `p`.
  have hp : Commute s (s * (g * s * g⁻¹)) := by
    have hsp : Commute (s⁻¹ * (s * (g * s * g⁻¹)) * s) (s * (g * s * g⁻¹)) := by
      rw [inv_eq_of_mul_eq_one_right hs', commute_iff_eq]
      simp [mul_assoc, hss, hs']
    exact Subgroup.mem_centralizer_singleton_iff.1
      (hG.mem_centralizer_of_conj_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.2 hsp))
  -- Hence `g * s * g⁻¹` commutes with `s`, and `g` centralizes `s`.
  have hq : Commute (g⁻¹⁻¹ * s * g⁻¹) s :=
    (commute_iff_eq _ _).2 (by simpa [mul_assoc, hss] using (congrArg (s * ·) hp.eq).symm)
  exact Subgroup.mem_centralizer_singleton_iff.1 (inv_mem_iff.1
    (hG.mem_centralizer_of_conj_mem_centralizer (Subgroup.mem_centralizer_singleton_iff.2 hq)))

/-- In a nonabelian CSA group, every nonidentity element has a conjugate that does not commute
with a given nonidentity element. -/
theorem IsCSA.exists_not_commute_conj (hG : IsCSA G) (h : ¬IsMulCommutative G) {u w : G}
    (hu : u ≠ 1) (hw : w ≠ 1) : ∃ f : G, ¬Commute (f⁻¹ * u * f) w := by
  by_contra! hf
  apply hu
  rw [← Subgroup.mem_bot, ← hG.center_eq_bot h, Subgroup.mem_center_iff]
  intro f
  have huw : Commute u w := by simpa using hf 1
  -- Every conjugate of `u` commutes with `u` through `w ≠ 1`, so every `f` centralizes `u`.
  exact Subgroup.mem_centralizer_singleton_iff.1 (hG.mem_centralizer_of_conj_mem_centralizer
    (Subgroup.mem_centralizer_singleton_iff.2 (hG.isCommTransitive _ w u hw (hf f) huw.symm).eq))

/-- In a CSA group, if `x` commutes with `y ≠ 1` but not with `t`, then the conjugate
`t⁻¹ * x * t` does not commute with `y`. -/
private theorem IsCSA.not_commute_conj_of_commute (hG : IsCSA G) {x y t : G} (hy : y ≠ 1)
    (hxy : Commute x y) (htx : ¬Commute t x) : ¬Commute (t⁻¹ * x * t) y := fun h =>
  htx (Subgroup.mem_centralizer_singleton_iff.1 (hG.mem_centralizer_of_conj_mem_centralizer
    (Subgroup.mem_centralizer_singleton_iff.2 (hG.isCommTransitive _ y x hy h hxy.symm).eq)))

/-- In a CSA group, if `b` does not commute with `c`, then for every `d ≠ 1` some nonidentity `t`
commuting with `b * c` makes the conjugate `t⁻¹ * c * t` not commute with `d`. -/
private theorem IsCSA.exists_conj_not_commute_conj (hG : IsCSA G) {b c d : G} (hd : d ≠ 1)
    (hbc : ¬Commute b c) : ∃ t, t ≠ 1 ∧ Commute t (b * c) ∧ ¬Commute (t⁻¹ * c * t) d := by
  have hsc : ¬Commute (b * c) c := fun h =>
    hbc ((IsRightRegular.all c).commute_mul_right_iff.1 h).symm
  generalize b * c = s at hsc ⊢
  have hs1 : s ≠ 1 := fun h => hsc (h ▸ Commute.one_left c)
  by_cases h : Commute (s⁻¹ * c * s) d
  swap
  · exact ⟨s, hs1, .refl s, h⟩
  -- Otherwise `t = s ^ 2` works; it is nontrivial since nonabelian CSA groups have no involutions.
  refine ⟨s ^ 2, fun h2 => hs1 (hG.eq_one_of_sq_eq_one (fun hG' => hbc (hG'.is_comm.comm b c)) h2),
    .pow_self s 2, ?_⟩
  have hsc' : ¬Commute s (s⁻¹ * c * s) := fun h' =>
    hsc (by simpa [mul_assoc] using (Commute.conj_iff s).2 h')
  have := hG.not_commute_conj_of_commute hd h hsc'
  simpa only [sq, mul_inv_rev, mul_assoc] using this

/-- [VAR-I], Lemma 10, case (5): in a CSA group, if no two consecutive entries of `b :: c :: r`
commute and `a ≠ 1`, then `b` and `c` have conjugates `b'` and `c'` with `b' * c' = b * c` such
that no two consecutive entries of `a :: b' :: c' :: r` commute. -/
private theorem IsCSA.exists_isConj_isChain_cons (hG : IsCSA G) {a b c : G} {r : List G}
    (ha : a ≠ 1) (h : (b :: c :: r).IsChain fun x y => ¬Commute x y) : ∃ b' c', IsConj b b' ∧
      IsConj c c' ∧ b' * c' = b * c ∧ (a :: b' :: c' :: r).IsChain fun x y => ¬Commute x y := by
  rw [List.isChain_cons_cons, List.isChain_cons] at h
  obtain ⟨hbc, hcr, hr⟩ := h
  by_cases hab : Commute a b
  swap
  · refine ⟨b, c, .refl b, .refl c, rfl, ?_⟩
    rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons]
    exact ⟨hab, hbc, hcr, hr⟩
  have hsb : ¬Commute (b * c) b := fun h => hbc ((IsLeftRegular.all b).commute_mul_left_iff.1 h)
  -- Conjugate `b` and `c` by some `t ≠ 1` commuting with `b * c` such that `t⁻¹ * c * t` does not
  -- commute with the next entry.
  obtain ⟨t, ht, hts, htr⟩ : ∃ t, t ≠ 1 ∧ Commute t (b * c) ∧
      ∀ d ∈ r.head?, ¬Commute (t⁻¹ * c * t) d := by
    obtain _ | ⟨d, r⟩ := r
    · exact ⟨b * c, fun h => hsb (h ▸ Commute.one_left b), .refl _, by simp⟩
    obtain ⟨t, ht, hts, htd⟩ := hG.exists_conj_not_commute_conj (d := d)
      (by rintro rfl; exact hcr 1 rfl (Commute.one_right c)) hbc
    exact ⟨t, ht, hts, by simpa using htd⟩
  refine ⟨t⁻¹ * b * t, t⁻¹ * c * t, isConj_iff.2 ⟨t⁻¹, by rw [inv_inv]⟩,
    isConj_iff.2 ⟨t⁻¹, by rw [inv_inv]⟩, ?_, ?_⟩
  · rw [← hts.inv_mul_cancel]
    group
  rw [List.isChain_cons_cons, List.isChain_cons_cons, List.isChain_cons]
  -- `t` does not commute with `b`, so the new first entry does not commute with `a`.
  exact ⟨fun h => hG.not_commute_conj_of_commute ha hab.symm
      (fun htb => hsb (hG.isCommTransitive _ t b ht hts.symm htb)) h.symm,
    fun h => hbc ((Commute.conj_iff t⁻¹).1 (by simpa using h)), htr, hr⟩

/-- In a CSA group, if `a` does not commute with `b` and `b` commutes with `c ≠ 1`, then `a` and
`b` have conjugates `a'` and `b'` with `a' * b' = a * b` such that `b'` does not commute with
`c`. -/
private theorem IsCSA.exists_isConj_mul_eq_not_commute (hG : IsCSA G) {a b c : G} (hc : c ≠ 1)
    (hab : ¬Commute a b) (hbc : Commute b c) : ∃ a' b', IsConj a a' ∧ IsConj b b' ∧
      a' * b' = a * b ∧ ¬Commute b' c :=
  ⟨(a * b)⁻¹ * a * (a * b), (a * b)⁻¹ * b * (a * b), isConj_iff.2 ⟨(a * b)⁻¹, by rw [inv_inv]⟩,
    isConj_iff.2 ⟨(a * b)⁻¹, by rw [inv_inv]⟩, by group,
    hG.not_commute_conj_of_commute hc hbc
      fun h => hab ((IsRightRegular.all b).commute_mul_right_iff.1 h).symm⟩

/-- The inductive step of [VAR-I], Proposition 3: in a CSA group, if a list `m` that is not a
commuting chain has entrywise conjugates `m'` with the same product and no two consecutive entries
commuting, then so has `a :: m` for every `a ≠ 1`. -/
private theorem IsCSA.exists_conj_cons (hG : IsCSA G) {a : G} {m m' : List G} (ha : a ≠ 1)
    (hmc : ¬m.IsChain Commute) (hmm' : List.Forall₂ IsConj m m') (hprod : m'.prod = m.prod)
    (hgp : m'.IsChain fun x y => ¬Commute x y) : ∃ l' : List G, List.Forall₂ IsConj (a :: m) l' ∧
      l'.prod = (a :: m).prod ∧ l'.IsChain fun x y => ¬Commute x y := by
  obtain _ | ⟨b, _ | ⟨c, r⟩⟩ := m'
  · cases hmm'
    exact absurd List.isChain_nil hmc
  · rcases hmm' with _ | ⟨_, _ | _⟩
    exact absurd (List.isChain_singleton _) hmc
  obtain ⟨b', c', hb', hc', hbc', hgp'⟩ := hG.exists_isConj_isChain_cons ha hgp
  rcases hmm' with _ | ⟨hb, _ | ⟨hc, hr⟩⟩
  refine ⟨_, .cons (.refl a) (.cons (hb.trans hb') (.cons (hc.trans hc') hr)), ?_, hgp'⟩
  simp only [List.prod_cons] at hprod ⊢
  rw [← mul_assoc b', hbc', mul_assoc, hprod]

/-- **Moving into general position.** In a CSA group, a list of nonidentity elements in which
some two consecutive entries do not commute can be replaced, entry by entry, by conjugates with
the same product in which no two consecutive entries commute. -/
theorem IsCSA.exists_conj_isChain_not_commute (hG : IsCSA G) {l : List G} (hl : ∀ a ∈ l, a ≠ 1)
    (hc : ¬l.IsChain Commute) : ∃ l' : List G, List.Forall₂ IsConj l l' ∧ l'.prod = l.prod ∧
      l'.IsChain fun a b => ¬Commute a b := by
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨_, rfl⟩
  induction n generalizing l with
  | zero => exact absurd (List.length_eq_zero_iff.1 hn ▸ List.IsChain.nil) hc
  | succ n ih =>
  obtain _ | ⟨a, m⟩ := l
  · simp at hn
  obtain ⟨ha, hm⟩ := List.forall_mem_cons.1 hl
  -- If the tail is not a commuting chain, move it into general position first.
  by_cases hmc : m.IsChain Commute
  swap
  · obtain ⟨m', hmm', hprod, hgp⟩ := ih hm hmc (by simpa using hn)
    exact hG.exists_conj_cons ha hmc hmm' hprod hgp
  obtain _ | ⟨b, _ | ⟨c, r⟩⟩ := m
  · exact absurd (List.isChain_singleton a) hc
  · exact ⟨[a, b], .cons (.refl a) (.cons (.refl b) .nil), rfl, by simpa using hc⟩
  -- Otherwise `a` does not commute with `b`, which commutes with `c`; conjugating `a` and `b`
  -- makes the tail not a commuting chain.
  obtain ⟨a', b', ha', hb', hab', hb'c⟩ := hG.exists_isConj_mul_eq_not_commute (hm c (by simp))
    (fun h => hc (List.isChain_cons_cons.2 ⟨h, hmc⟩)) (List.isChain_cons_cons.1 hmc).1
  have hmc' : ¬(b' :: c :: r).IsChain Commute := fun h => hb'c (List.isChain_cons_cons.1 h).1
  obtain ⟨m', hmm', hprod, hgp⟩ := ih (List.forall_mem_cons.2
    ⟨fun h => hm b (by simp) (isConj_one_left.1 (h ▸ hb')), (List.forall_mem_cons.1 hm).2⟩)
    hmc' (by simpa using hn)
  obtain ⟨l', hl', hprod', hgp'⟩ :=
    hG.exists_conj_cons (fun h => ha (isConj_one_left.1 (h ▸ ha'))) hmc' hmm' hprod hgp
  refine ⟨l', ?_, hprod'.trans (by simp only [List.prod_cons, ← mul_assoc, hab']), hgp'⟩
  rcases hl' with _ | ⟨ha'', _ | ⟨hb'', hr'⟩⟩
  exact .cons (ha'.trans ha'') (.cons (hb'.trans hb'') hr')

end Group
