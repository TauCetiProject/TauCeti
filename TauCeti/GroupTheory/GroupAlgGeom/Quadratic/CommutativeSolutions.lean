/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import TauCeti.GroupTheory.GroupAlgGeom.FreeDiscrimination
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination

/-!
# Radicals of standard quadratic equations all of whose solutions are commutative

Let `G` be a nonabelian fully residually free group and `S = 1` a standard quadratic equation over
`G` of one of the forms
`x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` (type (4), `n > 0`) or `c₁^{z₁} ⋯ c_m^{z_m} d = 1`
(type (2) of genus `0`), where `c^z = z⁻¹ c z`. Suppose that `S` has a solution `a` in `G` and that
all its solutions in `G` are commutative: at each of them, consecutive atoms commute. Then the
radical `R(S)` is the normal closure of the system `commutativeSystem x z c a`. With
`uⱼ = a(zⱼ)⁻¹ zⱼ` and `C` the centralizer of the elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` and `a(x_k)`, this
system consists of `x₁ ⋯ xₙ = a(x₁) ⋯ a(xₙ)` and of the commutators of the `x_k` and the `uⱼ` with
each other and with the elements of `C` ([IFT], Theorem 2 (7); [VAR-I], Corollary 3 and
Proposition 8 (4)). The proof follows [VAR-I]:

* At every solution all atoms commute with each other, so they lie in the abelian centralizer
  `C_G(d)`, and `C = C_G(d)`. Consecutive atoms commute, and commutation is transitive through
  nonidentity elements. A square `xₖ²` may be trivial, but then moving the values of the `xₖ`
  with trivial square to the front gives another solution, in which the nontrivial atoms are
  consecutive.
* So, by malnormality of `C_G(d)`, every solution sends `uⱼ` into `C_G(d)` and `zⱼ⁻¹ cⱼ zⱼ` to
  `a(zⱼ)⁻¹ cⱼ a(zⱼ)`, and by uniqueness of roots it satisfies `x₁ ⋯ xₙ = a(x₁) ⋯ a(xₙ)`. Conversely
  every solution of the system solves `S`: the equation and the system have the same solutions.
* The group of the system embeds over `G` in the free product of the extension
  `G(d, ℤ^{m + n})` of the centralizer of `d` with the free group on the variables, by
  `zⱼ ↦ a(zⱼ) tⱼ` and `x_k ↦ a(x_k) t_{m+k}`, the image of `x₁` being corrected so that the product
  relation holds. This group is discriminated by `G`, so the radical of the system is its normal
  closure.

The commutators are Mathlib's `⁅g, h⁆ = g h g⁻¹ h⁻¹`; their normal closures are the same as with the
convention `[g, h] = g⁻¹ h⁻¹ g h` of the sources. For one conjugated coefficient, the system is the
conjugate by `a(z)` of the system `⁅z a(z)⁻¹, h⁆`, `h ∈ C_G(c)`, of
`TauCeti.GroupAlgGeom.Quadratic.Rad_conjugacy_eq_normalClosure`, which is stated for one variable.

The hypothesis that `G` is nonabelian is needed because the set of variables may be larger than
the variables of `S`. Over `G = ℤ`, the commutator `⁅y, g⁆` with a variable `y` not occurring in
`z⁻¹ g z g⁻¹ = 1` lies in the radical but not in the normal closure of the system, as the map
`z ↦ 1`, `y ↦ t` to `ℤ ∗ ⟨t⟩` shows.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.commutativeSystem`: the system of [IFT], Theorem 2 (7), of a
  solution `a`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.mem_V_commutativeSystem_iff`: the solutions of the system.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_toWord_orientableCoeff_zero_of_forall_isCommutative`:
  the radical of `c₁^{z₁} ⋯ c_m^{z_m} d = 1` when all its solutions are commutative.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_toWord_nonorientableCoeff_of_forall_isCommutative`:
  the radical of `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` when all its solutions are commutative.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Theorem 2 (7).
* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Theorem 3 (2), and §2, Propositions 6–8 and Corollary 3.
-/

public section

open Monoid.Coprod Subgroup Group
open scoped commutatorElement

namespace TauCeti.GroupAlgGeom.Quadratic

open LimitGroup

variable {G X : Type*} [Group G]

/-! ### The system -/

/-- The system describing the solutions of `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` when all of them
are commutative, in terms of a fixed solution `a`: with `uⱼ = a(zⱼ)⁻¹ zⱼ` and `C` the centralizer
of the elements `cⱼ^{a(zⱼ)}` and `a(x_k)`, it consists of `x₁ ⋯ xₙ = a(x₁) ⋯ a(xₙ)` and of the
commutators of the `x_k` and the `uⱼ` with each other and with the elements of `C`. -/
def commutativeSystem {n m : ℕ} (x : Fin n → X) (z : Fin m → X) (c : Fin m → G) (a : X → G) :
    Set (GX G X) :=
  let ξ : Fin n → GX G X := fun k ↦ inr (FreeGroup.of (x k))
  let υ : Fin m → GX G X := fun j ↦ inl (a (z j))⁻¹ * inr (FreeGroup.of (z j))
  let C : Set G := centralizer
    (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k))
  {(List.ofFn ξ).prod * inl ((List.ofFn fun k ↦ a (x k)).prod)⁻¹} ∪
    (Set.range fun p : Fin n × Fin n ↦ ⁅ξ p.1, ξ p.2⁆) ∪
    (Set.range fun p : Fin m × Fin n ↦ ⁅υ p.1, ξ p.2⁆) ∪
    (Set.range fun p : Fin m × Fin m ↦ ⁅υ p.1, υ p.2⁆) ∪
    Set.image2 (fun k h ↦ ⁅ξ k, inl h⁆) Set.univ C ∪
    Set.image2 (fun j h ↦ ⁅υ j, inl h⁆) Set.univ C

/-- A point `v` solves `commutativeSystem x z c a` exactly when `v(x₁) ⋯ v(xₙ) = a(x₁) ⋯ a(xₙ)`
and the `v(x_k)` and the `a(zⱼ)⁻¹ v(zⱼ)` commute with each other and with the elements of the
centralizer `C`. -/
theorem mem_V_commutativeSystem_iff {H : Type*} [Group H] (ι : G →* H) {n m : ℕ}
    (x : Fin n → X) (z : Fin m → X) (c : Fin m → G) (a : X → G) (v : X → H) :
    v ∈ V ι (commutativeSystem x z c a) ↔
      (List.ofFn fun k ↦ v (x k)).prod = ι (List.ofFn fun k ↦ a (x k)).prod ∧
      (∀ k l, Commute (v (x k)) (v (x l))) ∧
      (∀ j k, Commute ((ι (a (z j)))⁻¹ * v (z j)) (v (x k))) ∧
      (∀ i j, Commute ((ι (a (z i)))⁻¹ * v (z i)) ((ι (a (z j)))⁻¹ * v (z j))) ∧
      (∀ k, ∀ h ∈ centralizer
        (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)),
          Commute (v (x k)) (ι h)) ∧
      ∀ j, ∀ h ∈ centralizer
        (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)),
          Commute ((ι (a (z j)))⁻¹ * v (z j)) (ι h) := by
  simp only [commutativeSystem, V_union, Set.mem_inter_iff, mem_V, Set.mem_singleton_iff,
    forall_eq, Set.forall_mem_range, Set.forall_mem_image2, Set.mem_univ, true_implies,
    SetLike.mem_coe, Prod.forall, map_mul, map_inv, map_list_prod, List.map_ofFn,
    Function.comp_def, eval_inl, eval_inr_of, map_commutatorElement,
    commutatorElement_eq_one_iff_commute, mul_inv_eq_one, and_assoc]

variable {n m : ℕ} {x : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G} {a : X → G}

/-! ### Commutation of the atoms of a solution -/

/-- The word `x₁² ⋯ xₙ² z₁⁻¹ c₁ z₁ ⋯ z_m⁻¹ c_m z_m d`. -/
private def sqConjWord (x : Fin n → X) (z : Fin m → X) (c : Fin m → G) (d : G) : GX G X :=
  (List.ofFn (fun k ↦ (inr (FreeGroup.of (x k)) : GX G X) ^ 2) ++
    List.ofFn fun j ↦ (inr (FreeGroup.of (z j)) : GX G X)⁻¹ * inl (c j) *
      inr (FreeGroup.of (z j))).prod * inl d

/-- The values of the atoms of `sqConjWord x z c d` at a point `v`. -/
private def atomVals (x : Fin n → X) (z : Fin m → X) (c : Fin m → G) (v : X → G) : List G :=
  List.ofFn (fun k ↦ v (x k) ^ 2) ++ List.ofFn fun j ↦ (v (z j))⁻¹ * c j * v (z j)

private theorem mem_V_sqConjWord_iff {v : X → G} :
    v ∈ V (.id G) {sqConjWord x z c d} ↔ (atomVals x z c v).prod * d = 1 := by
  simp [sqConjWord, atomVals, map_list_prod, Function.comp_def]

/-- In a commutative-transitive group, the elements of a `Commute`-chain of nonidentity elements
commute with its product. -/
private theorem commute_prod_of_isChain (hG : IsCommTransitive G) {L : List G}
    (hL : L.IsChain Commute) (h1 : ∀ g ∈ L, g ≠ 1) {g : G} (hg : g ∈ L) : Commute g L.prod := by
  -- Commutation between nonidentity elements is transitive.
  let R : G → G → Prop := fun a b ↦ Commute a b ∧ a ≠ 1 ∧ b ≠ 1
  have : Trans R R R :=
    ⟨fun hab hbc ↦ ⟨(isCommTransitive_iff G).1 hG _ _ _ hab.2.2 hab.1 hbc.1, hab.2.1, hbc.2.2⟩⟩
  have : Std.Symm (Commute : G → G → Prop) := ⟨fun _ _ h ↦ h.symm⟩
  have hR : L.IsChain R := hL.imp_of_mem_imp fun a b ha hb h ↦ ⟨h, h1 a ha, h1 b hb⟩
  exact Commute.list_prod_right _ _ fun g' hg' ↦
    (hR.pairwise.imp And.left).forall_of_forall (fun g _ ↦ Commute.refl g) hg hg'

/-- Dropping elements with trivial square from a list does not change the product of the
squares. -/
private theorem prod_map_sq_filter (p : G → Bool) (hp : ∀ b, p b = true → b ^ 2 = 1)
    (l : List G) : ((l.filter fun b ↦ !p b).map (· ^ 2)).prod = (l.map (· ^ 2)).prod := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases hb : p b <;> simp [hb, ih, hp b]

/-- Reordering the values of the `xₖ`, those selected by `p` first, gives a point whose atoms are
the squares of the selected values, then those of the others, then the conjugates of `v`. -/
private theorem exists_atomVals_eq_filter (inj : (Sum.elim x z).Injective) (v : X → G)
    (p : G → Bool) : ∃ w : X → G, atomVals x z c w =
      ((List.ofFn fun k ↦ v (x k)).filter p).map (· ^ 2) ++
        (((List.ofFn fun k ↦ v (x k)).filter fun b ↦ !p b).map (· ^ 2) ++
          List.ofFn fun j ↦ (v (z j))⁻¹ * c j * v (z j)) := by
  have hx : x.Injective := fun k l h ↦ Sum.inl_injective (inj h)
  set R := List.ofFn fun k ↦ v (x k)
  set R' := R.filter p ++ R.filter fun b ↦ !p b
  have hlen : R'.length = n := by
    rw [(List.filter_append_perm p R).length_eq, List.length_ofFn]
  refine ⟨Function.extend x (fun k : Fin n ↦ R'[k.val]) v, ?_⟩
  have hwx : (List.ofFn fun k ↦ Function.extend x (fun k : Fin n ↦ R'[k.val]) v (x k) ^ 2) =
      R'.map (· ^ 2) := by
    refine List.ext_getElem (by simp [hlen]) fun i _ _ ↦ ?_
    simp [hx.extend_apply]
  have hwz (j : Fin m) : Function.extend x (fun k : Fin n ↦ R'[k.val]) v (z j) = v (z j) :=
    Function.extend_apply' _ _ _ fun ⟨k, hk⟩ ↦ Sum.inl_ne_inr (inj hk)
  rw [atomVals, hwx, List.map_append, List.append_assoc]
  simp [hwz]

/-- If all solutions of `sqConjWord x z c d = 1` are commutative, then at every solution every
atom commutes with `d`. -/
private theorem commute_of_mem_atomVals (hG : IsCommTransitive G)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1)
    (hall : ∀ v ∈ V (.id G) {sqConjWord x z c d}, (atomVals x z c v).IsChain Commute)
    {v : X → G} (hv : v ∈ V (.id G) {sqConjWord x z c d}) {r : G}
    (hr : r ∈ atomVals x z c v) : Commute r d := by
  classical
  -- Move the values of the `xₖ` with trivial square to the front.
  set p : G → Bool := fun b ↦ decide (b ^ 2 = 1) with hp
  have hsq : ∀ b, p b = true → b ^ 2 = 1 := fun b hb ↦ by simpa [hp] using hb
  set R := List.ofFn fun k ↦ v (x k)
  set N := (R.filter fun b ↦ !p b).map (· ^ 2) ++ List.ofFn fun j ↦ (v (z j))⁻¹ * c j * v (z j)
  obtain ⟨w, hwN⟩ := exists_atomVals_eq_filter (c := c) inj v p
  have hd : N.prod = d⁻¹ := by
    have : (List.ofFn fun k ↦ v (x k) ^ 2) = R.map (· ^ 2) := by
      simp [R, List.map_ofFn, Function.comp_def]
    rw [← eq_inv_of_mul_eq_one_left (mem_V_sqConjWord_iff.1 hv), atomVals, this, List.prod_append,
      List.prod_append, prod_map_sq_filter p hsq]
  have hw : w ∈ V (.id G) {sqConjWord x z c d} := by
    rw [mem_V_sqConjWord_iff, hwN, List.prod_append, List.prod_eq_one, one_mul, hd,
      inv_mul_cancel]
    simp only [List.mem_map, List.mem_filter]
    rintro _ ⟨b, ⟨-, hb⟩, rfl⟩
    exact hsq b hb
  -- The remaining atoms of `w` form a chain of nonidentity elements with product `d⁻¹`.
  have hN1 : ∀ g ∈ N, g ≠ 1 := by
    simp only [N, List.mem_append, List.mem_map, List.mem_filter, List.mem_ofFn]
    rintro _ (⟨b, ⟨-, hb⟩, rfl⟩ | ⟨j, rfl⟩)
    · simpa [hp] using hb
    · simpa [mul_assoc, inv_mul_eq_one] using hc j
  rcases eq_or_ne r 1 with rfl | hr1
  · exact Commute.one_left d
  refine Commute.inv_right_iff.1 (hd ▸ commute_prod_of_isChain hG
    (hwN ▸ hall w hw).right_of_append hN1 ?_)
  simp only [atomVals, List.mem_append, List.mem_ofFn] at hr
  simp only [N, List.mem_append, List.mem_map, List.mem_filter, List.mem_ofFn, R]
  rcases hr with ⟨k, rfl⟩ | ⟨j, rfl⟩
  · exact .inl ⟨v (x k), ⟨⟨k, rfl⟩, by simpa [hp] using hr1⟩, rfl⟩
  · exact .inr ⟨j, rfl⟩

/-- Elements of the centralizer of `d ≠ 1` in a commutative-transitive group commute. -/
private theorem commute_of_mem_centralizer (hG : IsCommTransitive G) (hd : d ≠ 1) {g h : G}
    (hg : g ∈ centralizer {d}) (hh : h ∈ centralizer {d}) : Commute g h :=
  have := isCommTransitive_iff_centralizer_isMulCommutative.1 hG d hd
  setLike_mul_comm hg hh

/-- If all solutions are commutative, every solution sends the `xₖ` into `C_G(d)`. -/
private theorem mem_centralizer_of_mem_V (hG : IsFullyResiduallyFree G)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1)
    (hall : ∀ v ∈ V (.id G) {sqConjWord x z c d}, (atomVals x z c v).IsChain Commute)
    {v : X → G} (hv : v ∈ V (.id G) {sqConjWord x z c d}) (k : Fin n) :
    v (x k) ∈ centralizer {d} := by
  have := hG.isResiduallyFree.isMulTorsionFree
  have hk := commute_of_mem_atomVals hG.isCommTransitive inj hc hall hv
    (List.mem_append_left _ (List.mem_ofFn.2 ⟨k, rfl⟩))
  refine mem_centralizer_singleton_iff.2 ?_
  rcases eq_or_ne (v (x k) ^ 2) 1 with h1 | h1
  · simp [sq_eq_one.1 h1]
  · exact ((isCommTransitive_iff G).1 hG.isCommTransitive _ _ _ h1 (Commute.self_pow _ 2) hk).eq

/-- If all solutions are commutative, every solution sends the `zⱼ⁻¹ cⱼ zⱼ` into `C_G(d)`. -/
private theorem conj_mem_centralizer_of_mem_V (hG : IsCommTransitive G)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1)
    (hall : ∀ v ∈ V (.id G) {sqConjWord x z c d}, (atomVals x z c v).IsChain Commute)
    {v : X → G} (hv : v ∈ V (.id G) {sqConjWord x z c d}) (j : Fin m) :
    (v (z j))⁻¹ * c j * v (z j) ∈ centralizer {d} :=
  mem_centralizer_singleton_iff.2 (commute_of_mem_atomVals hG inj hc hall hv
    (List.mem_append_right _ (List.mem_ofFn.2 ⟨j, rfl⟩))).eq

/-- The centralizer `C` of the system of a solution `a` whose atoms lie in `C_G(d)` is `C_G(d)`. -/
private theorem centralizer_eq_of_mem_V (hG : IsCommTransitive G) (hd : d ≠ 1)
    (ha : a ∈ V (.id G) {sqConjWord x z c d}) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d}) :
    centralizer (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)) =
      centralizer {d} := by
  -- Not all the elements are trivial, since the atoms of `a` multiply to `d⁻¹ ≠ 1`.
  obtain ⟨g, hg, hg1⟩ : ∃ g ∈ (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪
      Set.range fun k ↦ a (x k)), g ≠ 1 := by
    by_contra! h
    refine hd ?_
    have h1 : (atomVals x z c a).prod = 1 := List.prod_eq_one fun g hg ↦ by
      simp only [atomVals, List.mem_append, List.mem_ofFn] at hg
      rcases hg with ⟨k, rfl⟩ | ⟨j, rfl⟩
      · simp [h _ (.inr ⟨k, rfl⟩)]
      · exact h _ (.inl ⟨j, rfl⟩)
    simpa [h1] using mem_V_sqConjWord_iff.1 ha
  have hgd : g ∈ centralizer {d} := by
    rcases hg with ⟨j, rfl⟩ | ⟨k, rfl⟩
    exacts [hb j, hs k]
  refine le_antisymm (fun h hh ↦ mem_centralizer_singleton_iff.2 ?_) fun h hh ↦ ?_
  · exact ((isCommTransitive_iff G).1 hG _ _ _ hg1 (mem_centralizer_iff.1 hh g hg).symm
      (mem_centralizer_singleton_iff.1 hgd)).eq
  · rw [mem_centralizer_iff]
    rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
    exacts [(commute_of_mem_centralizer hG hd (hb j) hh).eq,
      (commute_of_mem_centralizer hG hd (hs k) hh).eq]

/-! ### The equation and the system have the same solutions -/

/-- The square of a product of pairwise commuting elements is the product of their squares. -/
private theorem prod_ofFn_sq {f : Fin n → G} (h : ∀ k l, Commute (f k) (f l)) :
    (List.ofFn fun k ↦ f k ^ 2).prod = (List.ofFn f).prod ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih fun k l ↦ h _ _, (Commute.list_prod_right _ _ ?_).mul_pow]
    simp only [List.mem_ofFn]
    rintro _ ⟨k, rfl⟩
    exact h _ _

/-- If `a⁻¹ w` commutes with `a⁻¹ c a`, then `w⁻¹ c w = a⁻¹ c a`. -/
private theorem inv_mul_mul_eq_of_commute {a w c : G} (h : Commute (a⁻¹ * w) (a⁻¹ * c * a)) :
    w⁻¹ * c * w = a⁻¹ * c * a := by
  rw [← h.inv_mul_cancel]
  group

/-- A solution of the equation whose atoms lie in `C_G(d)` solves the system of a solution `a`
whose atoms lie in `C_G(d)`. -/
private theorem mem_V_commutativeSystem_of_mem_V (hG : IsFullyResiduallyFree G)
    (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) (ha : a ∈ V (.id G) {sqConjWord x z c d})
    (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d})
    {v : X → G} (hv : v ∈ V (.id G) {sqConjWord x z c d})
    (hvx : ∀ k, v (x k) ∈ centralizer {d})
    (hvz : ∀ j, (v (z j))⁻¹ * c j * v (z j) ∈ centralizer {d}) :
    v ∈ V (.id G) (commutativeSystem x z c a) := by
  have := hG.isResiduallyFree.isMulTorsionFree
  have hA {g h : G} (hg : g ∈ centralizer {d}) (hh : h ∈ centralizer {d}) : Commute g h :=
    commute_of_mem_centralizer hG.isCommTransitive hd hg hh
  -- By malnormality of `C_G(d)`, `uⱼ = a(zⱼ)⁻¹ v(zⱼ)` centralizes `d`.
  have hu (j : Fin m) : (a (z j))⁻¹ * v (z j) ∈ centralizer {d} := by
    have hb1 : (a (z j))⁻¹ * c j * a (z j) ≠ 1 := by simpa [mul_assoc, inv_mul_eq_one] using hc j
    refine inv_mem_iff.1 (hG.isCSA.mem_centralizer_of_commute_conj (hb j) hb1 (hb j) hb1 ?_)
    convert hA (hb j) (hvz j) using 1
    group
  rw [mem_V_commutativeSystem_iff, centralizer_eq_of_mem_V hG.isCommTransitive hd ha hs hb]
  refine ⟨?_, fun k l ↦ hA (hvx k) (hvx l), fun j k ↦ hA (hu j) (hvx k),
    fun i j ↦ hA (hu i) (hu j), fun k h hh ↦ hA (hvx k) hh, fun j h hh ↦ hA (hu j) hh⟩
  -- The products of the `xₖ` have the same square, and they commute.
  refine ((hA (list_prod_mem ?_) (list_prod_mem ?_)).pow_left_inj two_ne_zero).1 ?_
  · simpa using hvx
  · simpa using hs
  have h := (mem_V_sqConjWord_iff.1 hv).trans (mem_V_sqConjWord_iff.1 ha).symm
  simp only [atomVals, List.prod_append, fun j ↦ inv_mul_mul_eq_of_commute (hA (hu j) (hb j))] at h
  rw [← prod_ofFn_sq fun k l ↦ hA (hvx k) (hvx l), ← prod_ofFn_sq fun k l ↦ hA (hs k) (hs l)]
  exact mul_right_cancel (mul_right_cancel h)

/-- A solution of the system of a solution `a` whose atoms lie in `C_G(d)` solves the
equation. -/
private theorem mem_V_of_mem_V_commutativeSystem (hG : IsCommTransitive G) (hd : d ≠ 1)
    (ha : a ∈ V (.id G) {sqConjWord x z c d}) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d})
    {v : X → G} (hv : v ∈ V (.id G) (commutativeSystem x z c a)) :
    v ∈ V (.id G) {sqConjWord x z c d} := by
  rw [mem_V_commutativeSystem_iff, centralizer_eq_of_mem_V hG hd ha hs hb] at hv
  obtain ⟨h1, h2, -, -, -, h6⟩ := hv
  rw [mem_V_sqConjWord_iff, atomVals, List.prod_append]
  simp only [fun j ↦ inv_mul_mul_eq_of_commute (h6 j _ (hb j)), prod_ofFn_sq h2]
  rw [h1, MonoidHom.id_apply,
    ← prod_ofFn_sq fun k l ↦ commute_of_mem_centralizer hG hd (hs k) (hs l), ← List.prod_append]
  exact mem_V_sqConjWord_iff.1 ha

/-! ### The group of the system embeds in an extension of a centralizer -/

/-- A product of finitely many elements of `C × B`, for a commutative monoid `B`. -/
private theorem prod_ofFn_prod {B C : Type*} [Monoid C] [CommMonoid B] (f : Fin n → C × B) :
    (List.ofFn f).prod = ((List.ofFn fun k ↦ (f k).1).prod, ∏ k, (f k).2) := by
  refine Prod.ext ?_ ?_
  · simpa [List.map_ofFn, Function.comp_def] using map_list_prod (MonoidHom.fst C B) (List.ofFn f)
  · simpa [List.map_ofFn, Function.comp_def, List.prod_ofFn] using
      map_list_prod (MonoidHom.snd C B) (List.ofFn f)

/-- The exponents in `ℤ^{m + n}` of the new letters in the image of `x_k`: the letter `t_{m+k}`,
and for `k = 0` also the inverse of the product of all of them, so that they add up to `0`. -/
private def xExp (m n : ℕ) (k : Fin n) : Fin (m + n) → Multiplicative ℤ :=
  Pi.mulSingle (Fin.natAdd m k) (.ofAdd 1) *
    if (k : ℕ) = 0 then (∏ l : Fin n, Pi.mulSingle (Fin.natAdd m l) (.ofAdd 1))⁻¹ else 1

private theorem prod_xExp : ∏ k, xExp m n k = 1 := by
  rcases n with _ | n
  · simp
  · simp [xExp, Fin.prod_univ_succ]

/-- The solution of the system in `G(d, ℤ^{m + n}) ∗ F(X)` through which every solution
factors: `x_k ↦ a(x_k) t_{m+k}` (corrected at `k = 0`), `zⱼ ↦ a(zⱼ) tⱼ`, and every other variable
to itself. -/
private noncomputable def extPoint (x : Fin n → X) (z : Fin m → X) (a : X → G)
    (hs : ∀ k, a (x k) ∈ centralizer {d}) : X → GX (CentralizerExt d (m + n)) X :=
  Function.extend (Sum.elim x z)
    (Sum.elim (fun k ↦ inl (CentralizerExt.ofProd (⟨a (x k), hs k⟩, xExp m n k)))
      fun j ↦ inl (CentralizerExt.of (a (z j)) * CentralizerExt.t (Fin.castAdd n j)))
    fun y ↦ inr (FreeGroup.of y)

private theorem extPoint_x (inj : (Sum.elim x z).Injective) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (k : Fin n) :
    extPoint x z a hs (x k) = inl (CentralizerExt.ofProd (⟨a (x k), hs k⟩, xExp m n k)) :=
  inj.extend_apply _ _ (.inl k)

private theorem extPoint_z (inj : (Sum.elim x z).Injective) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (j : Fin m) : extPoint x z a hs (z j) =
      inl (CentralizerExt.of (a (z j)) * CentralizerExt.t (Fin.castAdd n j)) :=
  inj.extend_apply _ _ (.inr j)

/-- `extPoint` solves the system. -/
private theorem mem_V_extPoint (hG : IsCommTransitive G) (hd : d ≠ 1)
    (inj : (Sum.elim x z).Injective) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hC : centralizer
      (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)) =
        centralizer {d}) :
    extPoint x z a hs ∈ V (inl.comp CentralizerExt.of) (commutativeSystem x z c a) := by
  -- Everything in the image of `C_G(d) × ℤ^{m + n}` commutes.
  have hcomm (p q : centralizer {d} × (Fin (m + n) → Multiplicative ℤ)) :
      Commute (inl (CentralizerExt.ofProd p) : GX (CentralizerExt d (m + n)) X)
        (inl (CentralizerExt.ofProd q)) :=
    ((Commute.prod (Subtype.ext (commute_of_mem_centralizer hG hd p.1.property q.1.property).eq)
      (Commute.all _ _)).map _).map _
  have hz (j : Fin m) : ((inl.comp CentralizerExt.of) (a (z j)))⁻¹ * extPoint x z a hs (z j) =
      inl (CentralizerExt.ofProd (1, Pi.mulSingle (Fin.castAdd n j) (.ofAdd 1))) := by
    rw [extPoint_z inj, MonoidHom.comp_apply, map_mul, ← CentralizerExt.ofProd_mulSingle]
    exact inv_mul_cancel_left (G := GX (CentralizerExt d (m + n)) X) _ _
  have hι {h : G} (hh : h ∈ centralizer {d}) : (inl.comp CentralizerExt.of) h =
      (inl (CentralizerExt.ofProd (⟨h, hh⟩, 1)) : GX (CentralizerExt d (m + n)) X) := by
    simp
  rw [mem_V_commutativeSystem_iff, hC]
  refine ⟨?_, fun k l ↦ ?_, fun j k ↦ ?_, fun i j ↦ ?_, fun k h hh ↦ ?_, fun j h hh ↦ ?_⟩
  · have hx : (List.ofFn fun k ↦ extPoint x z a hs (x k)) =
        (List.ofFn fun k ↦ (⟨a (x k), hs k⟩, xExp m n k)).map (inl.comp CentralizerExt.ofProd) := by
      simp [extPoint_x inj, List.map_ofFn, Function.comp_def]
    rw [hx, ← map_list_prod, prod_ofFn_prod]
    simp [prod_xExp, List.map_ofFn, Function.comp_def]
  · rw [extPoint_x inj, extPoint_x inj]; exact hcomm _ _
  · rw [hz, extPoint_x inj]; exact hcomm _ _
  · rw [hz, hz]; exact hcomm _ _
  · rw [extPoint_x inj, hι hh]; exact hcomm _ _
  · rw [hz, hι hh]; exact hcomm _ _

/-- The images of the new letters under the homomorphism `G(d, ℤ^{m + n}) → H` given by a solution
`v` of the system: the `a(zⱼ)⁻¹ v(zⱼ)`, then the `a(x_k)⁻¹ v(x_k)`. -/
private def letterVals {H : Type*} [Group H] (ι : G →* H) (x : Fin n → X) (z : Fin m → X)
    (a : X → G) (v : X → H) : Fin (m + n) → H :=
  Fin.append (fun j ↦ (ι (a (z j)))⁻¹ * v (z j)) fun k ↦ (ι (a (x k)))⁻¹ * v (x k)

/-- At a solution of the system, the elements `letterVals` commute with `C_G(d)`. -/
private theorem commute_letterVals {H : Type*} [Group H] {ι : G →* H} {v : X → H}
    (hv : v ∈ V ι (commutativeSystem x z c a))
    (hC : centralizer
      (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)) =
        centralizer {d})
    (hG : IsCommTransitive G) (hd : d ≠ 1) (hs : ∀ k, a (x k) ∈ centralizer {d})
    {h : G} (hh : h ∈ centralizer {d}) (i : Fin (m + n)) :
    Commute (ι h) (letterVals ι x z a v i) := by
  rw [mem_V_commutativeSystem_iff, hC] at hv
  refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i
  · simpa [letterVals] using (hv.2.2.2.2.2 j h hh).symm
  · simpa [letterVals] using
      ((commute_of_mem_centralizer hG hd hh (hs k)).map ι).inv_right.mul_right
        (hv.2.2.2.2.1 k h hh).symm

/-- At a solution of the system, the elements `letterVals` commute with each other. -/
private theorem commute_letterVals_letterVals {H : Type*} [Group H] {ι : G →* H} {v : X → H}
    (hv : v ∈ V ι (commutativeSystem x z c a))
    (hC : centralizer
      (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)) =
        centralizer {d})
    (hG : IsCommTransitive G) (hd : d ≠ 1) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (i i' : Fin (m + n)) : Commute (letterVals ι x z a v i) (letterVals ι x z a v i') := by
  have hι {h : G} (hh : h ∈ centralizer {d}) (i : Fin (m + n)) :=
    commute_letterVals hv hC hG hd hs hh i
  rw [mem_V_commutativeSystem_iff, hC] at hv
  obtain ⟨-, h2, h3, h4, h5, h6⟩ := hv
  refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i
  · refine Fin.addCases (fun j' ↦ ?_) (fun l ↦ ?_) i'
    · simpa [letterVals] using h4 j j'
    · simpa [letterVals] using (h6 j _ (hs l)).inv_right.mul_right (h3 j l)
  · have hx : Commute (v (x k)) (letterVals ι x z a v i') := by
      refine Fin.addCases (fun j ↦ ?_) (fun l ↦ ?_) i'
      · simpa [letterVals] using (h3 j k).symm
      · simpa [letterVals] using (h5 k _ (hs l)).inv_right.mul_right (h2 k l)
    simpa [letterVals] using (hι (hs k) i').inv_left.mul_left hx

/-- Every solution `v` of the system in a group `H` factors through `extPoint`. -/
private theorem exists_comp_eval_extPoint {H : Type*} [Group H] (hG : IsCommTransitive G)
    (hd : d ≠ 1) (inj : (Sum.elim x z).Injective) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hC : centralizer
      (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)) =
        centralizer {d})
    {ι : G →* H} {v : X → H} (hv : v ∈ V ι (commutativeSystem x z c a)) :
    ∃ ψ : GX (CentralizerExt d (m + n)) X →* H,
      ψ.comp (eval (inl.comp CentralizerExt.of) (extPoint x z a hs)) = eval ι v := by
  classical
  set τ := letterVals ι x z a v
  have hτ := commute_letterVals_letterVals hv hC hG hd hs
  let ψK := CentralizerExt.lift ι τ hτ fun _ hh i ↦ commute_letterVals hv hC hG hd hs hh i
  have hψK (p : centralizer {d} × (Fin (m + n) → Multiplicative ℤ)) :
      ψK (CentralizerExt.ofProd p) = ι p.1 * zpowersPiHom τ hτ p.2 :=
    CentralizerExt.lift_ofProd _ _ _ _ p
  -- The product relation of the system says that the letters of the `xₖ` multiply to `1`.
  have hσ : zpowersPiHom τ hτ (∏ l : Fin n, Pi.mulSingle (Fin.natAdd m l) (.ofAdd 1)) = 1 := by
    have hx : (List.ofFn fun k ↦ v (x k)) = (List.ofFn fun k ↦ (⟨a (x k), hs k⟩,
        Pi.mulSingle (Fin.natAdd m k) (.ofAdd 1))).map (ψK.comp CentralizerExt.ofProd) := by
      simp [List.map_ofFn, Function.comp_def, hψK, τ, letterVals]
    have h1 := ((mem_V_commutativeSystem_iff ι x z c a v).1 hv).1
    rw [hx, ← map_list_prod, prod_ofFn_prod, MonoidHom.comp_apply, hψK] at h1
    simpa [Subgroup.val_list_prod, List.map_ofFn, Function.comp_def] using h1
  refine ⟨lift ψK (FreeGroup.lift v), hom_ext (MonoidHom.ext fun g ↦ ?_)
    (FreeGroup.ext_hom _ _ fun y ↦ ?_)⟩
  · simp [ψK, CentralizerExt.lift_of _ _ _ _ g]
  simp only [MonoidHom.comp_apply, eval_inr_of]
  by_cases hy : ∃ p, Sum.elim x z p = y
  · obtain ⟨k | j, rfl⟩ := hy
    · rw [Sum.elim_inl, extPoint_x inj, lift_apply_inl, hψK]
      simp only [xExp, map_mul, zpowersPiHom_mulSingle]
      split_ifs
      · rw [map_inv, hσ, inv_one, mul_one]
        simp [τ, letterVals]
      · rw [map_one, mul_one]
        simp [τ, letterVals]
    · rw [Sum.elim_inr, extPoint_z inj, lift_apply_inl, map_mul, CentralizerExt.lift_of,
        CentralizerExt.lift_t]
      simp [τ, letterVals]
  · simp [extPoint, Function.extend_apply' _ _ _ hy]

/-- The free product of an extension of the centralizer of `d ≠ 1` with a free group is
discriminated by a nonabelian fully residually free group `G`. -/
private theorem isDiscriminatedBy_inl_comp_of (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) (hd : d ≠ 1) (r : ℕ) :
    IsDiscriminatedBy (inl.comp CentralizerExt.of : G →* GX (CentralizerExt d r) X) (.id G) := by
  have hK : IsFullyResiduallyFree (CentralizerExt d r) := isFullyResiduallyFree_centralizerExt hG hd
  have hKna : ¬IsMulCommutative (CentralizerExt d r) := fun h ↦ hna ⟨⟨fun g g' ↦
    CentralizerExt.of_injective (u := d) (n := r)
      (by rw [map_mul, map_mul]; exact h.is_comm.comm _ _)⟩⟩
  exact ((GX.isDiscriminatedBy hK.isBP hK.isCSA hKna).comp CentralizerExt.of).trans
    (CentralizerExt.isDiscriminatedBy hG.isBP hG.isCSA hd)

/-- The group of the system is separated by `G`. -/
private theorem isSeparatedBy_coeff_commutativeSystem (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) (inj : (Sum.elim x z).Injective) (hd : d ≠ 1)
    (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hC : centralizer
      (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k)) =
        centralizer {d}) :
    IsSeparatedBy (SystemGroup.coeff (commutativeSystem x z c a)) (.id G) := by
  set T := commutativeSystem x z c a
  -- The generic point of `G_T` solves `T`, so it factors through `extPoint`.
  let ξ : X → SystemGroup G T := fun y ↦ ((inr (FreeGroup.of y) : GX G X) : SystemGroup G T)
  have hξ : eval (SystemGroup.coeff T) ξ = QuotientGroup.mk' (normalClosure T) :=
    hom_ext (MonoidHom.ext fun _ ↦ by simp) (FreeGroup.ext_hom _ _ fun _ ↦ by simp [ξ])
  obtain ⟨ψ, hψ⟩ := exists_comp_eval_extPoint hG.isCommTransitive hd inj hs hC (v := ξ) <|
    mem_V.2 fun t ht ↦ by
      rw [hξ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact subset_normalClosure ht
  refine (isDiscriminatedBy_inl_comp_of hG hna hd _).isSeparatedBy.of_injective
    (SystemGroup.evalGHom _ (mem_V_extPoint hG.isCommTransitive hd inj hs hC))
    (Function.LeftInverse.injective (g := ψ) fun w ↦ ?_)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
  simpa [hξ] using DFunLike.congr_fun hψ w

/-! ### The radical -/

private theorem Rad_sqConjWord_eq_normalClosure (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) (ha : a ∈ V (.id G) {sqConjWord x z c d})
    (hall : ∀ v ∈ V (.id G) {sqConjWord x z c d}, (atomVals x z c v).IsChain Commute) :
    Rad (.id G) {sqConjWord x z c d} = normalClosure (commutativeSystem x z c a) := by
  have hT := hG.isCommTransitive
  have hs := mem_centralizer_of_mem_V hG inj hc hall ha
  have hb := conj_mem_centralizer_of_mem_V hT inj hc hall ha
  refine (SystemGroup.isSeparatedBy_coeff_iff_of_subset (fun w hw ↦ mem_Rad.2 fun v hv ↦ ?_)
    fun t ht ↦ mem_Rad.2 fun v hv ↦ mem_V.1 (mem_V_commutativeSystem_of_mem_V hG hc hd ha hs hb
      hv (mem_centralizer_of_mem_V hG inj hc hall hv)
      (conj_mem_centralizer_of_mem_V hT inj hc hall hv)) t ht).1
    (isSeparatedBy_coeff_commutativeSystem hG hna inj hd hs
      (centralizer_eq_of_mem_V hT hd ha hs hb))
  rw [Set.mem_singleton_iff.1 hw]
  exact mem_V.1 (mem_V_of_mem_V_commutativeSystem hT hd ha hs hb hv) _ rfl

namespace Standard

/-- Over a nonabelian fully residually free group, if all solutions of
`c₁^{z₁} ⋯ c_m^{z_m} d = 1` are commutative, its radical is the normal closure of the system
`commutativeSystem` of a solution. -/
theorem Rad_toWord_orientableCoeff_zero_of_forall_isCommutative (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) {m : ℕ} {x y : Fin 0 → X} {z : Fin m → X} {c : Fin m → G} {d : G}
    (hm : 0 < 0 + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord},
      (orientableCoeff 0 m hm x y z inj c hc d hd).IsCommutative (.id G) v) :
    Rad (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord} =
      normalClosure (commutativeSystem Fin.elim0 z c a) := by
  have inj' : (Sum.elim (Fin.elim0 : Fin 0 → X) z).Injective :=
    Function.Injective.sumElim (fun p ↦ p.elim0) (fun _ _ h ↦ Sum.inr_injective (inj h))
      fun p ↦ p.elim0
  have hW : (orientableCoeff 0 m hm x y z inj c hc d hd).toWord = sqConjWord Fin.elim0 z c d := by
    simp [toWord_def, sqConjWord]
  rw [hW] at ha hall ⊢
  refine Rad_sqConjWord_eq_normalClosure hG hna inj' hc hd ha fun v hv ↦ ?_
  simpa [isCommutative_iff, atomVals, List.map_ofFn, Function.comp_def] using hall v hv

/-- Over a nonabelian fully residually free group, if all solutions of
`x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` are commutative, its radical is the normal closure of the
system `commutativeSystem` of a solution. -/
theorem Rad_toWord_nonorientableCoeff_of_forall_isCommutative (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) {n m : ℕ} {x : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}
    (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord},
      (nonorientableCoeff n m hn x z inj c hc d hd).IsCommutative (.id G) v) :
    Rad (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} =
      normalClosure (commutativeSystem x z c a) := by
  have hW : (nonorientableCoeff n m hn x z inj c hc d hd).toWord = sqConjWord x z c d := by
    simp [toWord_def, sqConjWord]
  rw [hW] at ha hall ⊢
  refine Rad_sqConjWord_eq_normalClosure hG hna inj hc hd ha fun v hv ↦ ?_
  simpa [isCommutative_iff, atomVals, List.map_ofFn, Function.comp_def] using hall v hv

end Standard

end TauCeti.GroupAlgGeom.Quadratic
