/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.LimitGroup.ResiduallyFree
import TauCeti.Algebra.BigOperators.Group.List
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Discrimination

/-!
# Radicals of standard quadratic equations all of whose solutions are commutative

Let `G` be a nonabelian fully residually free group and `S = 1` a standard quadratic equation over
`G` of one of the forms
`x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` (type (4), `n > 0`) or `c₁^{z₁} ⋯ c_m^{z_m} d = 1`
(type (2) of genus `0`, `m > 0`), where `c^z = z⁻¹ c z`, the variables are distinct, `cⱼ ≠ 1` and
`d ≠ 1`. Suppose that `S` has a solution `a` in `G` and that all its solutions in `G` are
commutative: at each of them, consecutive atoms commute. Then the radical `R(S)` is the normal
closure of the system `commutativeSystem x z c a`. With `uⱼ = a(zⱼ)⁻¹ zⱼ` and `C` the centralizer
of the elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` and `a(x_k)` (`commutativeSystemCentralizer x z c a`), this
system consists of `x₁ ⋯ xₙ = a(x₁) ⋯ a(xₙ)` and of the commutators of the `x_k` and the `uⱼ` with
each other and with the elements of `C`
([IFT], Theorem 2 (7); [VAR-I], Corollary 3 and Proposition 8 (4)). The proof follows [VAR-I]:

* At every solution all atoms commute with each other, so they lie in the abelian centralizer
  `C_G(d)`, and `C = C_G(d)` (`Group.IsCommTransitive.centralizer_eq_centralizer_singleton`;
  for the two forms of `S`,
  `Standard.commutativeSystemCentralizer_eq_of_forall_isCommutative_nonorientableCoeff` and
  `Standard.commutativeSystemCentralizer_eq_of_forall_isCommutative_orientableCoeff_zero`).
  Consecutive atoms commute, and commutation is transitive through
  nonidentity elements. A square `xₖ²` may be trivial, but then moving the values of the `xₖ`
  with trivial square to the front gives another solution, in which the nontrivial atoms are
  consecutive.
* So, by malnormality of `C_G(d)`, every solution sends `uⱼ` into `C_G(d)` and `zⱼ⁻¹ cⱼ zⱼ` to
  `a(zⱼ)⁻¹ cⱼ a(zⱼ)`, and by uniqueness of roots it satisfies `x₁ ⋯ xₙ = a(x₁) ⋯ a(xₙ)`. Conversely
  every solution of the system solves `S`: the equation and the system have the same solutions
  (`Standard.V_toWord_orientableCoeff_zero_of_forall_isCommutative` over a CSA group, and
  `Standard.V_toWord_nonorientableCoeff_of_forall_isCommutative` over a torsion-free CSA group).
* The group of the system embeds over `G`, as a retract, in the free product of the extension
  `G(d, ℤ^{m + n})` of the centralizer of `d` with the free group on the variables, by
  `zⱼ ↦ a(zⱼ) tⱼ` and `x_k ↦ a(x_k) t_{m+k}`, the image of `x₁` being corrected so that the product
  relation holds. This needs only `C = C_G(d)` and distinct variables
  (`TauCeti.GroupAlgGeom.Quadratic.commutativeSystemEmbedding`,
  `TauCeti.GroupAlgGeom.Quadratic.exists_leftInverse_commutativeSystemEmbedding`). The
  free product is discriminated by `G`
  (`TauCeti.LimitGroup.CentralizerExt.isDiscriminatedBy_inl_comp_of`), so the radical of the
  system is its normal closure
  (`TauCeti.GroupAlgGeom.Quadratic.Rad_commutativeSystem_eq_normalClosure`).

The commutators are Mathlib's `⁅g, h⁆ = g h g⁻¹ h⁻¹`; their normal closures are the same as with the
convention `[g, h] = g⁻¹ h⁻¹ g h` of the sources. For one conjugated coefficient, the system is the
conjugate by `a(z)` of the system `⁅z a(z)⁻¹, h⁆`, `h ∈ C_G(c)`, of
`TauCeti.GroupAlgGeom.Quadratic.Rad_conjugacy_eq_normalClosure`, which is stated for one variable.

The hypothesis that `G` is nonabelian is needed because the set of variables may be larger than
the variables of `S`. Over `G = ℤ`, the commutator `⁅y, g⁆` with a variable `y` not occurring in
`z⁻¹ g z g⁻¹ = 1` lies in the radical but not in the normal closure of the system, as the map
`z ↦ 1`, `y ↦ t` to `ℤ ∗ ⟨t⟩` shows.

## Main definitions

* `TauCeti.GroupAlgGeom.Quadratic.commutativeSystemCentralizer`: the centralizer `C` of the
  elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` and `a(x_k)`.
* `TauCeti.GroupAlgGeom.Quadratic.commutativeSystem`: the system of [IFT], Theorem 2 (7), of a
  point `a`.
* `TauCeti.GroupAlgGeom.Quadratic.commutativeSystemEmbedding`: when `C = C_G(d)`, the
  `G`-homomorphism from the group of the system to `G(d, ℤ^{m + n}) ∗ F(X)` given by
  `zⱼ ↦ a(zⱼ) tⱼ`, `x_k ↦ a(x_k) t_{m+k}` (corrected at `x₁`), and the identity on the other
  variables.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.mem_commutativeSystem_iff`: the relators of the system.
* `TauCeti.GroupAlgGeom.Quadratic.mem_V_commutativeSystem_iff`: the solutions of the system.
* `TauCeti.GroupAlgGeom.Quadratic.exists_leftInverse_commutativeSystemEmbedding`: the
  embedding has a left inverse over `G`, so the group of the system is a retract over `G` of
  `G(d, ℤ^{m + n}) ∗ F(X)` when `C = C_G(d)`.
* `TauCeti.GroupAlgGeom.Quadratic.Rad_commutativeSystem_eq_normalClosure`: over a nonabelian
  fully residually free group, the radical of the system is its normal closure when
  `C = C_G(d)`.
* `Standard.commutativeSystemCentralizer_eq_of_forall_isCommutative_orientableCoeff_zero`,
  `Standard.commutativeSystemCentralizer_eq_of_forall_isCommutative_nonorientableCoeff` (in
  `TauCeti.GroupAlgGeom.Quadratic`): `C = C_G(d)` at a solution of a standard equation `S` all
  of whose solutions are commutative.
* `Standard.V_toWord_orientableCoeff_zero_of_forall_isCommutative`,
  `Standard.V_toWord_nonorientableCoeff_of_forall_isCommutative` (in
  `TauCeti.GroupAlgGeom.Quadratic`): such an equation `S` and the system of a solution have the
  same solutions.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_toWord_orientableCoeff_zero_of_forall_isCommutative`:
  the radical of a standard equation `c₁^{z₁} ⋯ c_m^{z_m} d = 1` when all its solutions are
  commutative.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.Rad_toWord_nonorientableCoeff_of_forall_isCommutative`:
  the radical of a standard equation `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` when all its solutions
  are commutative.

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

/-- The centralizer `C` of the elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` and `a(x_k)`, built from variables `x_k`,
`zⱼ`, coefficients `cⱼ` and a point `a`. It is the centralizer appearing in the commutators of
`commutativeSystem x z c a`; for a standard equation all of whose solutions are commutative it is
the centralizer of `d`
(`Standard.commutativeSystemCentralizer_eq_of_forall_isCommutative_nonorientableCoeff`,
`Standard.commutativeSystemCentralizer_eq_of_forall_isCommutative_orientableCoeff_zero`). -/
def commutativeSystemCentralizer {n m : ℕ} (x : Fin n → X) (z : Fin m → X) (c : Fin m → G)
    (a : X → G) : Subgroup G :=
  centralizer (Set.range (fun j ↦ (a (z j))⁻¹ * c j * a (z j)) ∪ Set.range fun k ↦ a (x k))

/-- An element lies in `commutativeSystemCentralizer x z c a` exactly when it commutes with the
elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` and `a(x_k)`. -/
theorem mem_commutativeSystemCentralizer_iff {n m : ℕ} {x : Fin n → X} {z : Fin m → X}
    {c : Fin m → G} {a : X → G} {g : G} :
    g ∈ commutativeSystemCentralizer x z c a ↔
      (∀ j, Commute ((a (z j))⁻¹ * c j * a (z j)) g) ∧ ∀ k, Commute (a (x k)) g := by
  simp only [commutativeSystemCentralizer, mem_centralizer_iff, Set.mem_union, or_imp, forall_and,
    Commute, SemiconjBy, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]

/-- The system of relators built from variables `x_k`, `zⱼ`, coefficients `cⱼ` and a point `a`:
with `uⱼ = a(zⱼ)⁻¹ zⱼ` and `C = commutativeSystemCentralizer x z c a` the centralizer of the
elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` and `a(x_k)`, it consists of the relator `x₁ ⋯ xₙ (a(x₁) ⋯ a(xₙ))⁻¹`
and of the commutators of the `x_k` and the `uⱼ` with each other and with the elements of `C`.

Let `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (distinct variables, `cⱼ ≠ 1` and
`d ≠ 1`) over a nonabelian fully residually free group, all of whose solutions are commutative,
and let `a` be a solution. Then the equation and this system have the same solutions
(`Standard.V_toWord_nonorientableCoeff_of_forall_isCommutative`), and the normal closure of this
system is the radical of the equation
(`Standard.Rad_toWord_nonorientableCoeff_of_forall_isCommutative`; for `n = 0`, `m > 0`,
`Standard.V_toWord_orientableCoeff_zero_of_forall_isCommutative` and
`Standard.Rad_toWord_orientableCoeff_zero_of_forall_isCommutative`). -/
def commutativeSystem {n m : ℕ} (x : Fin n → X) (z : Fin m → X) (c : Fin m → G) (a : X → G) :
    Set (GX G X) :=
  let ξ : Fin n → GX G X := fun k ↦ inr (FreeGroup.of (x k))
  let υ : Fin m → GX G X := fun j ↦ inl (a (z j))⁻¹ * inr (FreeGroup.of (z j))
  let C : Set G := commutativeSystemCentralizer x z c a
  {(List.ofFn ξ).prod * inl ((List.ofFn fun k ↦ a (x k)).prod)⁻¹} ∪
    (Set.range fun p : Fin n × Fin n ↦ ⁅ξ p.1, ξ p.2⁆) ∪
    (Set.range fun p : Fin m × Fin n ↦ ⁅υ p.1, ξ p.2⁆) ∪
    (Set.range fun p : Fin m × Fin m ↦ ⁅υ p.1, υ p.2⁆) ∪
    Set.image2 (fun k h ↦ ⁅ξ k, inl h⁆) Set.univ C ∪
    Set.image2 (fun j h ↦ ⁅υ j, inl h⁆) Set.univ C

/-- `commutativeSystem x z c a` unfolded: the relator `x₁ ⋯ xₙ a(xₙ)⁻¹ ⋯ a(x₁)⁻¹` and the five
families of commutators. -/
theorem commutativeSystem_def {n m : ℕ} (x : Fin n → X) (z : Fin m → X) (c : Fin m → G)
    (a : X → G) :
    commutativeSystem x z c a =
      {(List.ofFn fun k ↦ (inr (FreeGroup.of (x k)) : GX G X)).prod *
          inl ((List.ofFn fun k ↦ a (x k)).prod)⁻¹} ∪
        (Set.range fun p : Fin n × Fin n ↦
          ⁅(inr (FreeGroup.of (x p.1)) : GX G X), inr (FreeGroup.of (x p.2))⁆) ∪
        (Set.range fun p : Fin m × Fin n ↦
          ⁅inl (a (z p.1))⁻¹ * inr (FreeGroup.of (z p.1)), inr (FreeGroup.of (x p.2))⁆) ∪
        (Set.range fun p : Fin m × Fin m ↦ ⁅inl (a (z p.1))⁻¹ * inr (FreeGroup.of (z p.1)),
          inl (a (z p.2))⁻¹ * inr (FreeGroup.of (z p.2))⁆) ∪
        Set.image2 (fun k h ↦ ⁅(inr (FreeGroup.of (x k)) : GX G X), inl h⁆) Set.univ
          (commutativeSystemCentralizer x z c a : Set G) ∪
        Set.image2 (fun j h ↦ ⁅(inl (a (z j))⁻¹ * inr (FreeGroup.of (z j)) : GX G X), inl h⁆)
          Set.univ (commutativeSystemCentralizer x z c a : Set G) :=
  (rfl)

/-- The relators of `commutativeSystem x z c a`: `x₁ ⋯ xₙ a(xₙ)⁻¹ ⋯ a(x₁)⁻¹` and the commutators
of the `x_k` and the `uⱼ = a(zⱼ)⁻¹ zⱼ` with each other and with the elements of the centralizer
`C`. -/
theorem mem_commutativeSystem_iff {n m : ℕ} {x : Fin n → X} {z : Fin m → X} {c : Fin m → G}
    {a : X → G} {w : GX G X} :
    w ∈ commutativeSystem x z c a ↔
      w = (List.ofFn fun k ↦ (inr (FreeGroup.of (x k)) : GX G X)).prod *
          inl ((List.ofFn fun k ↦ a (x k)).prod)⁻¹ ∨
        (∃ k l, ⁅(inr (FreeGroup.of (x k)) : GX G X), inr (FreeGroup.of (x l))⁆ = w) ∨
        (∃ j k, ⁅inl (a (z j))⁻¹ * inr (FreeGroup.of (z j)), inr (FreeGroup.of (x k))⁆ = w) ∨
        (∃ i j, ⁅inl (a (z i))⁻¹ * inr (FreeGroup.of (z i)),
          inl (a (z j))⁻¹ * inr (FreeGroup.of (z j))⁆ = w) ∨
        (∃ k, ∃ h ∈ commutativeSystemCentralizer x z c a,
          ⁅(inr (FreeGroup.of (x k)) : GX G X), inl h⁆ = w) ∨
        ∃ j, ∃ h ∈ commutativeSystemCentralizer x z c a,
          ⁅inl (a (z j))⁻¹ * inr (FreeGroup.of (z j)), inl h⁆ = w := by
  simp only [commutativeSystem_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_range,
    Prod.exists, Set.mem_image2, Set.mem_univ, true_and, SetLike.mem_coe, or_assoc]

/-- Over a coefficient map `ι : G →* H`, a point `v : X → H` solves `commutativeSystem x z c a`
exactly when `v(x₁) ⋯ v(xₙ) = ι(a(x₁) ⋯ a(xₙ))` and the `v(x_k)` and the `ι(a(zⱼ))⁻¹ v(zⱼ)`
commute with each other and with the images `ι(h)` of the elements `h` of the centralizer `C`. -/
theorem mem_V_commutativeSystem_iff {H : Type*} [Group H] (ι : G →* H) {n m : ℕ}
    (x : Fin n → X) (z : Fin m → X) (c : Fin m → G) (a : X → G) (v : X → H) :
    v ∈ V ι (commutativeSystem x z c a) ↔
      (List.ofFn fun k ↦ v (x k)).prod = ι (List.ofFn fun k ↦ a (x k)).prod ∧
      (∀ k l, Commute (v (x k)) (v (x l))) ∧
      (∀ j k, Commute ((ι (a (z j)))⁻¹ * v (z j)) (v (x k))) ∧
      (∀ i j, Commute ((ι (a (z i)))⁻¹ * v (z i)) ((ι (a (z j)))⁻¹ * v (z j))) ∧
      (∀ k, ∀ h ∈ commutativeSystemCentralizer x z c a, Commute (v (x k)) (ι h)) ∧
      ∀ j, ∀ h ∈ commutativeSystemCentralizer x z c a,
        Commute ((ι (a (z j)))⁻¹ * v (z j)) (ι h) := by
  simp only [commutativeSystem_def, V_union, Set.mem_inter_iff, mem_V, Set.mem_singleton_iff,
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
  set p : G → Bool := fun b ↦ b ^ 2 == 1 with hp
  have hsq : ∀ b, p b = true → b ^ 2 = 1 := fun b hb ↦ by simpa [hp] using hb
  set R := List.ofFn fun k ↦ v (x k)
  set N := (R.filter fun b ↦ !p b).map (· ^ 2) ++ List.ofFn fun j ↦ (v (z j))⁻¹ * c j * v (z j)
  obtain ⟨w, hwN⟩ := exists_atomVals_eq_filter (c := c) inj v p
  have hd : N.prod = d⁻¹ := by
    have : (List.ofFn fun k ↦ v (x k) ^ 2) = R.map (· ^ 2) := by
      simp [R, List.map_ofFn, Function.comp_def]
    -- The squares dropped by the filter are trivial.
    have hf : (R.filter fun b ↦ !p b).map (· ^ 2) = (R.map (· ^ 2)).filter (· != 1) := by
      simp [List.filter_map, Function.comp_def, hp, bne]
    rw [← eq_inv_of_mul_eq_one_left (mem_V_sqConjWord_iff.1 hv), atomVals, this, List.prod_append,
      List.prod_append, hf, List.prod_filter_bne_one]
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
  refine Commute.inv_right_iff.1 (hd ▸ hG.commute_list_prod_of_isChain
    (hwN ▸ hall w hw).right_of_append hN1 ?_)
  simp only [atomVals, List.mem_append, List.mem_ofFn] at hr
  simp only [N, List.mem_append, List.mem_map, List.mem_filter, List.mem_ofFn, R]
  rcases hr with ⟨k, rfl⟩ | ⟨j, rfl⟩
  · exact .inl ⟨v (x k), ⟨⟨k, rfl⟩, by simpa [hp] using hr1⟩, rfl⟩
  · exact .inr ⟨j, rfl⟩

/-- If all solutions are commutative, every solution sends the `xₖ` into `C_G(d)`. -/
private theorem mem_centralizer_of_mem_V [IsMulTorsionFree G] (hG : IsCommTransitive G)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1)
    (hall : ∀ v ∈ V (.id G) {sqConjWord x z c d}, (atomVals x z c v).IsChain Commute)
    {v : X → G} (hv : v ∈ V (.id G) {sqConjWord x z c d}) (k : Fin n) :
    v (x k) ∈ centralizer {d} := by
  have hk := commute_of_mem_atomVals hG inj hc hall hv
    (List.mem_append_left _ (List.mem_ofFn.2 ⟨k, rfl⟩))
  refine mem_centralizer_singleton_iff.2 ?_
  rcases eq_or_ne (v (x k) ^ 2) 1 with h1 | h1
  · simp [sq_eq_one.1 h1]
  · exact ((isCommTransitive_iff G).1 hG _ _ _ h1 (Commute.self_pow _ 2) hk).eq

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
    commutativeSystemCentralizer x z c a = centralizer {d} := by
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
  refine hG.centralizer_eq_centralizer_singleton hd ?_ hg hg1
  rintro _ (⟨j, rfl⟩ | ⟨k, rfl⟩)
  exacts [hb j, hs k]

/-! ### The equation and the system have the same solutions -/

/-- By malnormality of `C_G(d)`, a point `v` whose conjugates `v(zⱼ)⁻¹ cⱼ v(zⱼ)` lie in `C_G(d)`
sends `uⱼ = a(zⱼ)⁻¹ zⱼ` into `C_G(d)`, if the `a(zⱼ)⁻¹ cⱼ a(zⱼ)` lie in `C_G(d)`. -/
private theorem inv_mul_mem_centralizer (hG : IsCSA G) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1)
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d}) {v : X → G}
    (hvz : ∀ j, (v (z j))⁻¹ * c j * v (z j) ∈ centralizer {d}) (j : Fin m) :
    (a (z j))⁻¹ * v (z j) ∈ centralizer {d} := by
  have hb1 : (a (z j))⁻¹ * c j * a (z j) ≠ 1 := by simpa [mul_assoc, inv_mul_eq_one] using hc j
  refine inv_mem_iff.1 (hG.mem_centralizer_of_commute_conj (hb j) hb1 (hb j) hb1 ?_)
  convert hG.isCommTransitive.commute_of_mem_centralizer_singleton hd (hb j) (hvz j) using 1
  group

/-- A point whose atoms lie in `C_G(d)`, with `v(x₁) ⋯ v(xₙ) = a(x₁) ⋯ a(xₙ)`, solves the system
of a solution `a` whose atoms lie in `C_G(d)`. -/
private theorem mem_V_commutativeSystem_of_prod_eq (hG : IsCSA G) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) (ha : a ∈ V (.id G) {sqConjWord x z c d}) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d}) {v : X → G}
    (hvx : ∀ k, v (x k) ∈ centralizer {d})
    (hvz : ∀ j, (v (z j))⁻¹ * c j * v (z j) ∈ centralizer {d})
    (hprod : (List.ofFn fun k ↦ v (x k)).prod = (List.ofFn fun k ↦ a (x k)).prod) :
    v ∈ V (.id G) (commutativeSystem x z c a) := by
  have hA {g h : G} (hg : g ∈ centralizer {d}) (hh : h ∈ centralizer {d}) : Commute g h :=
    hG.isCommTransitive.commute_of_mem_centralizer_singleton hd hg hh
  have hu := inv_mul_mem_centralizer hG hc hd hb hvz
  rw [mem_V_commutativeSystem_iff, centralizer_eq_of_mem_V hG.isCommTransitive hd ha hs hb]
  exact ⟨hprod, fun k l ↦ hA (hvx k) (hvx l), fun j k ↦ hA (hu j) (hvx k),
    fun i j ↦ hA (hu i) (hu j), fun k h hh ↦ hA (hvx k) hh, fun j h hh ↦ hA (hu j) hh⟩

/-- At a solution `v` of the equation whose atoms lie in `C_G(d)`, `v(x₁) ⋯ v(xₙ)` and
`a(x₁) ⋯ a(xₙ)` have the same square in the abelian group `C_G(d)`, so they are equal when `G` is
torsion-free. -/
private theorem prod_eq_of_mem_V [IsMulTorsionFree G] (hG : IsCSA G) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) (ha : a ∈ V (.id G) {sqConjWord x z c d}) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d}) {v : X → G}
    (hv : v ∈ V (.id G) {sqConjWord x z c d}) (hvx : ∀ k, v (x k) ∈ centralizer {d})
    (hvz : ∀ j, (v (z j))⁻¹ * c j * v (z j) ∈ centralizer {d}) :
    (List.ofFn fun k ↦ v (x k)).prod = (List.ofFn fun k ↦ a (x k)).prod := by
  have hA {g h : G} (hg : g ∈ centralizer {d}) (hh : h ∈ centralizer {d}) : Commute g h :=
    hG.isCommTransitive.commute_of_mem_centralizer_singleton hd hg hh
  refine ((hA (list_prod_mem ?_) (list_prod_mem ?_)).pow_left_inj two_ne_zero).1 ?_
  · simpa using hvx
  · simpa using hs
  have h := (mem_V_sqConjWord_iff.1 hv).trans (mem_V_sqConjWord_iff.1 ha).symm
  have hconj (j : Fin m) : (v (z j))⁻¹ * c j * v (z j) = (a (z j))⁻¹ * c j * a (z j) := by
    rw [← (hA (inv_mul_mem_centralizer hG hc hd hb hvz j) (hb j)).inv_mul_cancel]
    group
  simp only [atomVals, List.prod_append, hconj, List.ofFn_eq_map,
    List.prod_map_pow_of_pairwise_commute (List.pairwise_of_forall fun k l ↦ hA (hvx k) (hvx l)),
    List.prod_map_pow_of_pairwise_commute (List.pairwise_of_forall fun k l ↦ hA (hs k) (hs l))] at h
  simpa only [List.ofFn_eq_map] using mul_right_cancel (mul_right_cancel h)

/-- A solution of the system of a solution `a` whose atoms lie in `C_G(d)` solves the
equation. -/
private theorem mem_V_of_mem_V_commutativeSystem (hG : IsCommTransitive G) (hd : d ≠ 1)
    (ha : a ∈ V (.id G) {sqConjWord x z c d}) (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hb : ∀ j, (a (z j))⁻¹ * c j * a (z j) ∈ centralizer {d})
    {v : X → G} (hv : v ∈ V (.id G) (commutativeSystem x z c a)) :
    v ∈ V (.id G) {sqConjWord x z c d} := by
  rw [mem_V_commutativeSystem_iff, centralizer_eq_of_mem_V hG hd ha hs hb] at hv
  obtain ⟨h1, h2, -, -, -, h6⟩ := hv
  have hconj (j : Fin m) : (v (z j))⁻¹ * c j * v (z j) = (a (z j))⁻¹ * c j * a (z j) := by
    have h : Commute ((a (z j))⁻¹ * v (z j)) ((a (z j))⁻¹ * c j * a (z j)) := h6 j _ (hb j)
    rw [← h.inv_mul_cancel]
    group
  -- The products of the squares of the `xₖ` are the squares of their products.
  rw [mem_V_sqConjWord_iff, ← mem_V_sqConjWord_iff.1 ha]
  simp only [atomVals, List.prod_append, hconj, mul_left_inj, List.ofFn_eq_map,
    List.prod_map_pow_of_pairwise_commute (List.pairwise_of_forall h2),
    List.prod_map_pow_of_pairwise_commute (List.pairwise_of_forall fun k l ↦
      hG.commute_of_mem_centralizer_singleton hd (hs k) (hs l))]
  simpa [List.ofFn_eq_map] using congrArg (· ^ 2) h1

/-! ### The group of the system embeds in an extension of a centralizer -/

/-- If the centralizer `C` of the system is `C_G(d)`, the `a(x_k)` commute with `C_G(d)`. -/
private theorem commute_of_centralizer_eq
    (hC : commutativeSystemCentralizer x z c a = centralizer {d})
    (k : Fin n) {h : G} (hh : h ∈ centralizer {d}) : Commute (a (x k)) h :=
  mem_centralizer_iff.1 (hC.ge hh) _ (.inr ⟨k, rfl⟩)

/-- If the centralizer `C` of the system is `C_G(d)`, the `a(x_k)` lie in `C_G(d)`. -/
private theorem mem_centralizer_of_centralizer_eq
    (hC : commutativeSystemCentralizer x z c a = centralizer {d})
    (k : Fin n) : a (x k) ∈ centralizer {d} :=
  mem_centralizer_singleton_iff.2 <|
    commute_of_centralizer_eq hC k (mem_centralizer_singleton_iff.2 (.refl d))

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
private theorem mem_V_extPoint (inj : (Sum.elim x z).Injective)
    (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hC : commutativeSystemCentralizer x z c a = centralizer {d}) :
    extPoint x z a hs ∈ V (inl.comp CentralizerExt.of) (commutativeSystem x z c a) := by
  -- Elements of the image of `C_G(d) × ℤ^{m + n}` commute when their `C_G(d)` parts do.
  have hcomm {p q : centralizer {d} × (Fin (m + n) → Multiplicative ℤ)}
      (h : Commute (p.1 : G) q.1) :
      Commute (inl (CentralizerExt.ofProd p) : GX (CentralizerExt d (m + n)) X)
        (inl (CentralizerExt.ofProd q)) :=
    ((Commute.prod (Subtype.ext h.eq) (Commute.all _ _)).map _).map _
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
    rw [hx, ← map_list_prod, ← Prod.mk.eta (p := List.prod _)]
    simp [prod_xExp, List.map_ofFn, Function.comp_def, List.prod_ofFn]
  · rw [extPoint_x inj, extPoint_x inj]; exact hcomm (commute_of_centralizer_eq hC k (hs l))
  · rw [hz, extPoint_x inj]; exact hcomm (.one_left _)
  · rw [hz, hz]; exact hcomm (.one_left _)
  · rw [extPoint_x inj, hι hh]; exact hcomm (commute_of_centralizer_eq hC k hh)
  · rw [hz, hι hh]; exact hcomm (.one_left _)

/-- The images of the new letters under the homomorphism `G(d, ℤ^{m + n}) → H` given by a solution
`v` of the system: the `a(zⱼ)⁻¹ v(zⱼ)`, then the `a(x_k)⁻¹ v(x_k)`. -/
private def letterVals {H : Type*} [Group H] (ι : G →* H) (x : Fin n → X) (z : Fin m → X)
    (a : X → G) (v : X → H) : Fin (m + n) → H :=
  Fin.append (fun j ↦ (ι (a (z j)))⁻¹ * v (z j)) fun k ↦ (ι (a (x k)))⁻¹ * v (x k)

/-- At a solution of the system, the elements `letterVals` commute with `C_G(d)`. -/
private theorem commute_letterVals {H : Type*} [Group H] {ι : G →* H} {v : X → H}
    (hv : v ∈ V ι (commutativeSystem x z c a))
    (hC : commutativeSystemCentralizer x z c a = centralizer {d})
    {h : G} (hh : h ∈ centralizer {d}) (i : Fin (m + n)) :
    Commute (ι h) (letterVals ι x z a v i) := by
  rw [mem_V_commutativeSystem_iff, hC] at hv
  refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) i
  · simpa [letterVals] using (hv.2.2.2.2.2 j h hh).symm
  · simpa [letterVals] using
      ((commute_of_centralizer_eq hC k hh).symm.map ι).inv_right.mul_right
        (hv.2.2.2.2.1 k h hh).symm

/-- At a solution of the system, the elements `letterVals` commute with each other. -/
private theorem commute_letterVals_letterVals {H : Type*} [Group H] {ι : G →* H} {v : X → H}
    (hv : v ∈ V ι (commutativeSystem x z c a))
    (hC : commutativeSystemCentralizer x z c a = centralizer {d})
    (i i' : Fin (m + n)) : Commute (letterVals ι x z a v i) (letterVals ι x z a v i') := by
  have hs := mem_centralizer_of_centralizer_eq hC
  have hι {h : G} (hh : h ∈ centralizer {d}) (i : Fin (m + n)) := commute_letterVals hv hC hh i
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
private theorem exists_comp_eval_extPoint {H : Type*} [Group H] (inj : (Sum.elim x z).Injective)
    (hs : ∀ k, a (x k) ∈ centralizer {d})
    (hC : commutativeSystemCentralizer x z c a = centralizer {d})
    {ι : G →* H} {v : X → H} (hv : v ∈ V ι (commutativeSystem x z c a)) :
    ∃ ψ : GX (CentralizerExt d (m + n)) X →* H,
      ψ.comp (eval (inl.comp CentralizerExt.of) (extPoint x z a hs)) = eval ι v := by
  classical
  set τ := letterVals ι x z a v
  have hτ := commute_letterVals_letterVals hv hC
  let ψK := CentralizerExt.lift ι τ hτ fun _ hh i ↦ commute_letterVals hv hC hh i
  have hψK (p : centralizer {d} × (Fin (m + n) → Multiplicative ℤ)) :
      ψK (CentralizerExt.ofProd p) = ι p.1 * zpowersPiHom τ hτ p.2 :=
    CentralizerExt.lift_ofProd _ _ _ _ p
  -- The product relation of the system says that the letters of the `xₖ` multiply to `1`.
  have hσ : zpowersPiHom τ hτ (∏ l : Fin n, Pi.mulSingle (Fin.natAdd m l) (.ofAdd 1)) = 1 := by
    have hx : (List.ofFn fun k ↦ v (x k)) = (List.ofFn fun k ↦ (⟨a (x k), hs k⟩,
        Pi.mulSingle (Fin.natAdd m k) (.ofAdd 1))).map (ψK.comp CentralizerExt.ofProd) := by
      simp [List.map_ofFn, Function.comp_def, hψK, τ, letterVals]
    have h1 := ((mem_V_commutativeSystem_iff ι x z c a v).1 hv).1
    rw [hx, ← map_list_prod, MonoidHom.comp_apply, hψK] at h1
    simpa [Subgroup.val_list_prod, List.map_ofFn, Function.comp_def, List.prod_ofFn] using h1
  refine ⟨lift ψK (FreeGroup.lift v), hom_ext (MonoidHom.ext fun g ↦ by simp [ψK])
    (FreeGroup.ext_hom _ _ fun y ↦ ?_)⟩
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

/-- The element `(g, xExp m n k)` of `C_G(d) × ℤ^{m + n}` is `g t_{m+k}` in `G(d, ℤ^{m + n})`,
times `(t_{m+1} ⋯ t_{m+n})⁻¹` for the first variable. -/
private theorem ofProd_xExp {g : G} (hg : g ∈ centralizer {d}) (k : Fin n) :
    (CentralizerExt.ofProd (⟨g, hg⟩, xExp m n k) : CentralizerExt d (m + n)) =
      CentralizerExt.of g * CentralizerExt.t (Fin.natAdd m k) *
        if (k : ℕ) = 0 then (List.ofFn fun l ↦ CentralizerExt.t (Fin.natAdd m l)).prod⁻¹
        else 1 := by
  rw [CentralizerExt.ofProd_apply, xExp, map_mul, zpowersPiHom_mulSingle, mul_assoc]
  split_ifs
  · rw [map_inv, ← List.prod_ofFn, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · simp

/-- The `G`-homomorphism from the group of `commutativeSystem x z c a` to the free product
`G(d, ℤ^{m + n}) ∗ F(X)` of the extension of the centralizer of `d` with the free group on the
variables given by `zⱼ ↦ a(zⱼ) tⱼ`, `x_k ↦ a(x_k) t_{m+k}` for `k > 1`,
`x₁ ↦ a(x₁) t_{m+1} (t_{m+1} ⋯ t_{m+n})⁻¹`, and every other variable to itself. It is defined when
the variables `x_k`, `zⱼ` are distinct and the centralizer `C` of the system is the centralizer of
`d`. It has a left inverse over `G` (`exists_leftInverse_commutativeSystemEmbedding`), so it embeds
the group of the system. -/
noncomputable def commutativeSystemEmbedding (inj : (Sum.elim x z).Injective)
    (hC : commutativeSystemCentralizer x z c a = centralizer {d}) :
    GHom (SystemGroup.coeff (commutativeSystem x z c a))
      (inl.comp CentralizerExt.of : G →* GX (CentralizerExt d (m + n)) X) :=
  SystemGroup.evalGHom _ (mem_V_extPoint inj (mem_centralizer_of_centralizer_eq hC) hC)

section Generators

variable {inj : (Sum.elim x z).Injective}
  {hC : commutativeSystemCentralizer x z c a = centralizer {d}}

/-- `commutativeSystemEmbedding` sends `x_k` to `a(x_k) t_{m+k}`, times `(t_{m+1} ⋯ t_{m+n})⁻¹` for
the first variable (the index `k : Fin n` starts at `0`). -/
@[simp]
theorem commutativeSystemEmbedding_mk_inr_of_x (k : Fin n) :
    commutativeSystemEmbedding inj hC
        ((inr (FreeGroup.of (x k)) : GX G X) : SystemGroup G (commutativeSystem x z c a)) =
      inl (CentralizerExt.of (a (x k)) * CentralizerExt.t (Fin.natAdd m k) *
        if (k : ℕ) = 0 then (List.ofFn fun l ↦ CentralizerExt.t (Fin.natAdd m l)).prod⁻¹
        else 1) := by
  rw [commutativeSystemEmbedding, SystemGroup.evalGHom_mk, eval_inr_of, extPoint_x inj, ofProd_xExp]

/-- `commutativeSystemEmbedding` sends `zⱼ` to `a(zⱼ) tⱼ`. -/
@[simp]
theorem commutativeSystemEmbedding_mk_inr_of_z (j : Fin m) :
    commutativeSystemEmbedding inj hC
        ((inr (FreeGroup.of (z j)) : GX G X) : SystemGroup G (commutativeSystem x z c a)) =
      inl (CentralizerExt.of (a (z j)) * CentralizerExt.t (Fin.castAdd n j)) := by
  rw [commutativeSystemEmbedding, SystemGroup.evalGHom_mk, eval_inr_of, extPoint_z inj]

/-- `commutativeSystemEmbedding` fixes every variable other than the `x_k` and the `zⱼ`. -/
@[simp]
theorem commutativeSystemEmbedding_mk_inr_of_of_forall_ne {y : X} (hx : ∀ k, x k ≠ y)
    (hz : ∀ j, z j ≠ y) :
    commutativeSystemEmbedding inj hC
        ((inr (FreeGroup.of y) : GX G X) : SystemGroup G (commutativeSystem x z c a)) =
      inr (FreeGroup.of y) := by
  rw [commutativeSystemEmbedding, SystemGroup.evalGHom_mk, eval_inr_of, extPoint,
    Function.extend_apply' _ _ _ (by rintro ⟨k | j, h⟩; exacts [hx k h, hz j h])]

end Generators

/-- If the centralizer `C` of the system is the centralizer of `d`, `commutativeSystemEmbedding`
has a left inverse over `G`: the group of the system `commutativeSystem x z c a` is a retract over
`G` of the free product `G(d, ℤ^{m + n}) ∗ F(X)` of the extension of the centralizer of `d` with
the free group on the variables. -/
theorem exists_leftInverse_commutativeSystemEmbedding (inj : (Sum.elim x z).Injective)
    (hC : commutativeSystemCentralizer x z c a = centralizer {d}) :
    ∃ ψ : GHom (inl.comp CentralizerExt.of : G →* GX (CentralizerExt d (m + n)) X)
        (SystemGroup.coeff (commutativeSystem x z c a)),
      Function.LeftInverse ψ (commutativeSystemEmbedding inj hC) := by
  set T := commutativeSystem x z c a
  have hs := mem_centralizer_of_centralizer_eq hC
  -- The generic point of `G_T` solves `T`, so it factors through `extPoint`.
  let ξ : X → SystemGroup G T := fun y ↦ ((inr (FreeGroup.of y) : GX G X) : SystemGroup G T)
  have hξ : eval (SystemGroup.coeff T) ξ = QuotientGroup.mk' (normalClosure T) :=
    hom_ext (MonoidHom.ext fun _ ↦ by simp) (FreeGroup.ext_hom _ _ fun _ ↦ by simp [ξ])
  obtain ⟨ψ, hψ⟩ := exists_comp_eval_extPoint inj hs hC (v := ξ) <| mem_V.2 fun t ht ↦ by
    rw [hξ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact subset_normalClosure ht
  refine ⟨⟨ψ, fun g ↦ ?_⟩, fun w ↦ ?_⟩
  · simpa using DFunLike.congr_fun hψ (inl g)
  · obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [commutativeSystemEmbedding, SystemGroup.evalGHom_mk, GHom.coe_mk]
    simpa [hξ] using DFunLike.congr_fun hψ w

/-- If the centralizer `C` of the system is the centralizer of `d`, `commutativeSystemEmbedding`
is injective. -/
theorem commutativeSystemEmbedding_injective (inj : (Sum.elim x z).Injective)
    (hC : commutativeSystemCentralizer x z c a = centralizer {d}) :
    Function.Injective (commutativeSystemEmbedding inj hC) :=
  (exists_leftInverse_commutativeSystemEmbedding inj hC).choose_spec.injective

/-! ### The radical -/

/-- Let `G` be a nonabelian fully residually free group, `d ≠ 1`, and the variables `x_k`, `zⱼ`
distinct. If the centralizer `C` of the system is the centralizer of `d`, then the radical of
`commutativeSystem x z c a` is its normal closure: its group embeds over `G` in
`G(d, ℤ^{m + n}) ∗ F(X)`, which is discriminated by `G`. -/
theorem Rad_commutativeSystem_eq_normalClosure (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) (inj : (Sum.elim x z).Injective) (hd : d ≠ 1)
    (hC : commutativeSystemCentralizer x z c a = centralizer {d}) :
    Rad (.id G) (commutativeSystem x z c a) = normalClosure (commutativeSystem x z c a) :=
  (SystemGroup.isSeparatedBy_coeff_iff _).1
    ((CentralizerExt.isDiscriminatedBy_inl_comp_of hG hna hd).isSeparatedBy.of_injective _
      (commutativeSystemEmbedding_injective inj hC))

namespace Standard

/-! ### The standard equations -/

private theorem toWord_orientableCoeff_zero_eq_sqConjWord {m : ℕ} {x y : Fin 0 → X}
    {z : Fin m → X} {c : Fin m → G} {d : G} (hm : 0 < 0 + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (orientableCoeff 0 m hm x y z inj c hc d hd).toWord = sqConjWord Fin.elim0 z c d := by
  simp [toWord_def, sqConjWord]

/-- In genus `0` the injectivity hypothesis of `orientableCoeff` gives the injectivity of the
variables `Sum.elim Fin.elim0 z` of `sqConjWord Fin.elim0 z c d`. -/
private theorem injective_elim0_of_orientableCoeff_zero {m : ℕ} {x y : Fin 0 → X}
    {z : Fin m → X} (inj : (Sum.elim (Sum.elim x y) z).Injective) :
    (Sum.elim (Fin.elim0 : Fin 0 → X) z).Injective :=
  Sum.elim_injective.2 ⟨isEmptyElim, inj.comp Sum.inr_injective, isEmptyElim⟩

private theorem isCommutative_orientableCoeff_zero_iff {m : ℕ} {x y : Fin 0 → X}
    {z : Fin m → X} {c : Fin m → G} {d : G} {hm : 0 < 0 + m}
    {inj : (Sum.elim (Sum.elim x y) z).Injective} {hc : ∀ j, c j ≠ 1} {hd : d ≠ 1}
    {v : X → G} :
    (orientableCoeff 0 m hm x y z inj c hc d hd).IsCommutative (.id G) v ↔
      (atomVals Fin.elim0 z c v).IsChain Commute := by
  simp [isCommutative_iff, atomVals, List.map_ofFn, Function.comp_def]

private theorem toWord_nonorientableCoeff_eq_sqConjWord (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    (nonorientableCoeff n m hn x z inj c hc d hd).toWord = sqConjWord x z c d := by
  simp [toWord_def, sqConjWord]

private theorem isCommutative_nonorientableCoeff_iff {hn : 0 < n}
    {inj : (Sum.elim x z).Injective} {hc : ∀ j, c j ≠ 1} {hd : d ≠ 1} {v : X → G} :
    (nonorientableCoeff n m hn x z inj c hc d hd).IsCommutative (.id G) v ↔
      (atomVals x z c v).IsChain Commute := by
  simp [isCommutative_iff, atomVals, List.map_ofFn, Function.comp_def]

/-- Let `c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (`m > 0`, distinct variables `zⱼ`,
`cⱼ ≠ 1` and `d ≠ 1`) over a commutative transitive group `G`. If all its solutions are
commutative, then at every solution `a` the centralizer of the elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)` is the
centralizer of `d`: this is the centralizer `C` of `commutativeSystem Fin.elim0 z c a`. -/
theorem commutativeSystemCentralizer_eq_of_forall_isCommutative_orientableCoeff_zero
    (hG : IsCommTransitive G) {m : ℕ} {x y : Fin 0 → X} {z : Fin m → X} {c : Fin m → G} {d : G}
    (hm : 0 < 0 + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord},
      (orientableCoeff 0 m hm x y z inj c hc d hd).IsCommutative (.id G) v) :
    commutativeSystemCentralizer Fin.elim0 z c a = centralizer {d} := by
  rw [toWord_orientableCoeff_zero_eq_sqConjWord] at ha hall
  exact centralizer_eq_of_mem_V hG hd ha isEmptyElim
    (conj_mem_centralizer_of_mem_V hG
      (injective_elim0_of_orientableCoeff_zero inj) hc
      (fun v hv ↦ isCommutative_orientableCoeff_zero_iff.1 (hall v hv)) ha)

/-- Let `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (`n > 0`, distinct variables,
`cⱼ ≠ 1` and `d ≠ 1`) over a torsion-free commutative transitive group `G`. If all its solutions
are commutative, then at every solution `a` the centralizer of the elements `a(zⱼ)⁻¹ cⱼ a(zⱼ)`
and `a(x_k)` is the centralizer of `d`: this is the centralizer `C` of
`commutativeSystem x z c a`. -/
theorem commutativeSystemCentralizer_eq_of_forall_isCommutative_nonorientableCoeff
    [IsMulTorsionFree G] (hG : IsCommTransitive G) {n m : ℕ} {x : Fin n → X} {z : Fin m → X}
    {c : Fin m → G} {d : G} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord},
      (nonorientableCoeff n m hn x z inj c hc d hd).IsCommutative (.id G) v) :
    commutativeSystemCentralizer x z c a = centralizer {d} := by
  rw [toWord_nonorientableCoeff_eq_sqConjWord] at ha hall
  have hall' := fun v hv ↦ isCommutative_nonorientableCoeff_iff.1 (hall v hv)
  exact centralizer_eq_of_mem_V hG hd ha (mem_centralizer_of_mem_V hG inj hc hall' ha)
    (conj_mem_centralizer_of_mem_V hG inj hc hall' ha)

/-- Let `c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (`m > 0`, distinct variables `zⱼ`,
`cⱼ ≠ 1` and `d ≠ 1`) over a CSA group `G`, with a solution `a`. If all its solutions are
commutative, it has the same solutions as `commutativeSystem Fin.elim0 z c a`. -/
theorem V_toWord_orientableCoeff_zero_of_forall_isCommutative (hG : IsCSA G) {m : ℕ}
    {x y : Fin 0 → X} {z : Fin m → X} {c : Fin m → G} {d : G} (hm : 0 < 0 + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord},
      (orientableCoeff 0 m hm x y z inj c hc d hd).IsCommutative (.id G) v) :
    V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord} =
      V (.id G) (commutativeSystem Fin.elim0 z c a) := by
  rw [toWord_orientableCoeff_zero_eq_sqConjWord] at ha hall ⊢
  have hb {v : X → G} (hv : v ∈ V (.id G) {sqConjWord Fin.elim0 z c d}) :=
    conj_mem_centralizer_of_mem_V hG.isCommTransitive
      (injective_elim0_of_orientableCoeff_zero inj) hc
      (fun v hv ↦ isCommutative_orientableCoeff_zero_iff.1 (hall v hv)) hv
  refine Set.ext fun v ↦ ⟨fun hv ↦ mem_V_commutativeSystem_of_prod_eq hG hc hd ha isEmptyElim
    (hb ha) isEmptyElim (hb hv) (by simp),
    mem_V_of_mem_V_commutativeSystem hG.isCommTransitive hd ha isEmptyElim (hb ha)⟩

/-- Let `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (`n > 0`, distinct variables,
`cⱼ ≠ 1` and `d ≠ 1`) over a torsion-free CSA group `G`, with a solution `a`. If all its solutions
are commutative, it has the same solutions as `commutativeSystem x z c a`. -/
theorem V_toWord_nonorientableCoeff_of_forall_isCommutative [IsMulTorsionFree G] (hG : IsCSA G)
    {n m : ℕ} {x : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G} (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord},
      (nonorientableCoeff n m hn x z inj c hc d hd).IsCommutative (.id G) v) :
    V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} =
      V (.id G) (commutativeSystem x z c a) := by
  rw [toWord_nonorientableCoeff_eq_sqConjWord] at ha hall ⊢
  have hT := hG.isCommTransitive
  have hall' := fun v hv ↦ isCommutative_nonorientableCoeff_iff.1 (hall v hv)
  have hs := mem_centralizer_of_mem_V hT inj hc hall' ha
  have hb := conj_mem_centralizer_of_mem_V hT inj hc hall' ha
  refine Set.ext fun v ↦ ⟨fun hv ↦ ?_, mem_V_of_mem_V_commutativeSystem hT hd ha hs hb⟩
  have hvx := mem_centralizer_of_mem_V hT inj hc hall' hv
  have hvz := conj_mem_centralizer_of_mem_V hT inj hc hall' hv
  exact mem_V_commutativeSystem_of_prod_eq hG hc hd ha hs hb hvx hvz
    (prod_eq_of_mem_V hG hc hd ha hs hb hv hvx hvz)

/-- Let `c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (`m > 0`, distinct variables `zⱼ`,
`cⱼ ≠ 1` and `d ≠ 1`) over a nonabelian fully residually free group `G`, with a solution `a`. If
all its solutions are commutative, its radical is the normal closure of
`commutativeSystem Fin.elim0 z c a`. -/
theorem Rad_toWord_orientableCoeff_zero_of_forall_isCommutative (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) {m : ℕ} {x y : Fin 0 → X} {z : Fin m → X} {c : Fin m → G} {d : G}
    (hm : 0 < 0 + m)
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord},
      (orientableCoeff 0 m hm x y z inj c hc d hd).IsCommutative (.id G) v) :
    Rad (.id G) {(orientableCoeff 0 m hm x y z inj c hc d hd).toWord} =
      normalClosure (commutativeSystem Fin.elim0 z c a) := by
  rw [Rad_def, V_toWord_orientableCoeff_zero_of_forall_isCommutative hG.isCSA hm inj hc hd ha hall,
    ← Rad_def]
  exact Rad_commutativeSystem_eq_normalClosure hG hna
    (injective_elim0_of_orientableCoeff_zero inj) hd
    (commutativeSystemCentralizer_eq_of_forall_isCommutative_orientableCoeff_zero
      hG.isCommTransitive hm inj hc hd ha hall)

/-- Let `x₁² ⋯ xₙ² c₁^{z₁} ⋯ c_m^{z_m} d = 1` be a standard equation (`n > 0`, distinct variables,
`cⱼ ≠ 1` and `d ≠ 1`) over a nonabelian fully residually free group `G`, with a solution `a`. If
all its solutions are commutative, its radical is the normal closure of
`commutativeSystem x z c a`. -/
theorem Rad_toWord_nonorientableCoeff_of_forall_isCommutative (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) {n m : ℕ} {x : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}
    (hn : 0 < n)
    (inj : (Sum.elim x z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) {a : X → G}
    (ha : a ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord})
    (hall : ∀ v ∈ V (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord},
      (nonorientableCoeff n m hn x z inj c hc d hd).IsCommutative (.id G) v) :
    Rad (.id G) {(nonorientableCoeff n m hn x z inj c hc d hd).toWord} =
      normalClosure (commutativeSystem x z c a) := by
  have := hG.isResiduallyFree.isMulTorsionFree
  rw [Rad_def, V_toWord_nonorientableCoeff_of_forall_isCommutative hG.isCSA hn inj hc hd ha hall,
    ← Rad_def]
  exact Rad_commutativeSystem_eq_normalClosure hG hna inj hd
    (commutativeSystemCentralizer_eq_of_forall_isCommutative_nonorientableCoeff
      hG.isCommTransitive hn inj hc hd ha hall)

end Standard

end TauCeti.GroupAlgGeom.Quadratic
