/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Basic
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Iterated
import TauCeti.GroupTheory.GroupAlgGeom.Abelian
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Regular
import TauCeti.GroupTheory.GroupAlgGeom.Separated
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.FreeProduct
import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Coordinate groups of `x₁² x₂² = 1` and `x₁² x₂² x₃² = 1`

Let `G` be a fully residually free group and `X` a finite set of variables. The non-orientable
standard quadratic equations `x₁² x₂² = 1` and `x₁² x₂² x₃² = 1` without coefficients have only
commutative solutions in `G`:

* `G` has unique roots, so every solution of `x₁² x₂² = 1` has `x₂ = x₁⁻¹`.
* By Lyndon's theorem in free groups, `G` satisfies Vaught's condition
  (`TauCeti.LimitGroup.IsResiduallyFree.isVaught`); it is also torsion-free, so every solution of
  `x₁² x₂² x₃² = 1` consists of pairwise commuting `x₁`, `x₂`, `x₃` with `x₁ x₂ x₃ = 1`
  (`Group.IsVaught.mul_mul_eq_one_of_sq_mul_sq_mul_sq_eq_one`).

So the radicals of both equations are larger than their normal closures. If `G` is not abelian,
they are described by these relations:

* the radical of `x₁² x₂² = 1` is the normal closure of `x₁ x₂`, the kernel of the substitution
  `x₂ ↦ x₁⁻¹`, and its coordinate group is `G ∗ F(X ∖ {x₂})`;
* the radical of `x₁² x₂² x₃² = 1` is the kernel of the map to `G[X] ∗ ℤ²` sending `x₁`, `x₂` to
  the generators `a₁`, `a₂` of `ℤ²` and `x₃` to `(a₁ a₂)⁻¹`, and its coordinate group is
  `G ∗ ℤ² ∗ F(X ∖ {x₁, x₂, x₃})`.

If `G` is abelian, both radicals also contain the commutator subgroup of `G[X]`, and both
coordinate groups are of the form `G × ℤᵏ`.

In every case the coordinate group embeds, over `G`, in an iterated extension of centralizers of
`G`; this embedding, not the description of the radical, is what is stated here. For nonabelian
`G`, the free `G`-group `G[X]` embeds in one extension of a centralizer of `G` and `G[X] ∗ ℤ²` in
one more (`TauCeti.LimitGroup.exists_ice_embedding_GX`,
`TauCeti.LimitGroup.exists_ice_embedding_coprod_pi_of_exists_ice_embedding`). Every solution
factors through the maps to these groups described above, so their kernels lie in the radicals,
and the coordinate groups embed with them
(`TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_ker_le_Rad`). For abelian `G` the
embedding is `TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_isMulCommutative`.

These are the cases (4) and (5) of the radicals of consistent standard quadratic equations over a
freely discriminated group, whose printed formulas in [IFT] omit the relations `x₁ x₂ = 1` and
`x₁ x₂ x₃ = 1` (and, for abelian `G`, the commutators with the coefficients), and two of the
low-genus cases of the embedding theorem of [VAR-I].

## Main results

* `Standard.exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_two`: the coordinate
  group of `x₁² x₂² = 1` embeds, over `G`, in an iterated extension of centralizers of `G`.
* `Standard.exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_three`: the same for
  `x₁² x₂² x₃² = 1`.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1,
  Theorem 1, and §3, Lemma 16.
* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §2.7, Theorem 2 (4), (5).
* R. C. Lyndon, *The equation `a²b² = c²` in free groups*, Michigan Math. J. 6 (1959).
-/

public section

open Monoid.Coprod

namespace TauCeti.GroupAlgGeom.Quadratic.Standard

open LimitGroup

universe u

variable {G : Type u} [Group G] {X : Type*}

-- Over a nonabelian fully residually free group, every solution of `x₁² x₂² = 1` factors through
-- the substitution `x₂ ↦ x₁⁻¹` of `G[X]`, which embeds in an extension of a centralizer.
private theorem exists_ice_embedding_coordGroup_sq_mul_sq (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) [Countable X] {x : Fin 2 → X} (hx : x.Injective) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {(nonorientable 2 two_pos x hx).toWord}) j),
      Function.Injective f := by
  classical
  rw [show (nonorientable (G := G) 2 two_pos x hx).toWord =
      inr (FreeGroup.of (x 0)) ^ 2 * inr (FreeGroup.of (x 1)) ^ 2 by
    simp [toWord_def, List.ofFn_succ]]
  have := hG.isResiduallyFree.hasUniqueRoots
  let p : X → GX G X :=
    Function.update (fun y => inr (FreeGroup.of y)) (x 1) (inr (FreeGroup.of (x 0)))⁻¹
  refine exists_ice_embedding_coordGroup_of_ker_le_Rad hG (exists_ice_embedding_GX hG hna X)
    (evalGHom inl p) (by simp [p, hx.ne zero_ne_one]) fun w hw => mem_Rad.2 fun v hv => ?_
  -- By unique roots `v x₁ = (v x₂)⁻¹`, so `v` factors through the substitution.
  have hv₁ : v (x 0) = (v (x 1))⁻¹ := by
    simpa [mul_eq_one_iff_eq_inv, ← inv_pow, (pow_left_injective two_ne_zero).eq_iff] using
      (mem_V.1 hv) _ rfl
  have hfac : (eval (.id G) v).comp (evalGHom inl p : GX G X →* GX G X) = eval (.id G) v :=
    GX.ext_hom (fun g => by simp) fun y => by by_cases hy : y = x 1 <;> simp [p, hy, hv₁]
  rw [← hfac, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hw, map_one]

-- Over a nonabelian fully residually free group, every solution of `x₁² x₂² x₃² = 1` factors
-- through the map `G[X] →* G[X] ∗ ℤ²` sending `x₁`, `x₂` to the generators `a₁`, `a₂` of `ℤ²` and
-- `x₃` to `(a₁ a₂)⁻¹`.
private theorem exists_ice_embedding_coordGroup_sq_mul_sq_mul_sq (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) [Countable X] {x : Fin 3 → X} (hx : x.Injective) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {(nonorientable 3 three_pos x hx).toWord}) j),
      Function.Injective f := by
  rw [show (nonorientable (G := G) 3 three_pos x hx).toWord = inr (FreeGroup.of (x 0)) ^ 2 *
      inr (FreeGroup.of (x 1)) ^ 2 * inr (FreeGroup.of (x 2)) ^ 2 by
    simp [toWord_def, List.ofFn_succ, mul_assoc]]
  let a : Fin 2 → Fin 2 → Multiplicative ℤ := fun i => Pi.mulSingle i (.ofAdd 1)
  let p : X → Monoid.Coprod (GX G X) (Fin 2 → Multiplicative ℤ) := Function.extend x
    (fun i => inr (![a 0, a 1, (a 0 * a 1)⁻¹] i)) fun y => inl (inr (FreeGroup.of y))
  -- `x₁² x₂² x₃²` goes to `a₁² a₂² (a₁ a₂)⁻² = 1` in `ℤ²`.
  have ha : a 0 ^ 2 * a 1 ^ 2 * ((a 0 * a 1)⁻¹) ^ 2 = 1 := by rw [inv_pow, mul_pow, mul_inv_cancel]
  refine exists_ice_embedding_coordGroup_of_ker_le_Rad hG
    (exists_ice_embedding_coprod_pi_of_exists_ice_embedding hG hna
      (exists_ice_embedding_GX hG hna X) 2) (evalGHom _ p)
    (by simpa [p, hx.extend_apply] using congrArg (inr : _ →* Monoid.Coprod (GX G X) _) ha)
    fun w hw => mem_Rad.2 fun v hv => ?_
  -- By Vaught's condition and torsion-freeness, `v x₁`, `v x₂` commute and `v x₁ v x₂ v x₃ = 1`.
  have := hG.isResiduallyFree.isMulTorsionFree
  have hsq : v (x 0) ^ 2 * v (x 1) ^ 2 * v (x 2) ^ 2 = 1 := by simpa using (mem_V.1 hv) _ rfl
  have h01 := ((Group.isVaught_iff G).1 hG.isResiduallyFree.isVaught _ _ _ hsq).1
  have hv₃ := hG.isResiduallyFree.isVaught.mul_mul_eq_one_of_sq_mul_sq_mul_sq_eq_one hsq
  let τ : Fin 2 → G := ![v (x 0), v (x 1)]
  have hτ : ∀ i j, Commute (τ i) (τ j) := by simp [τ, Fin.forall_fin_two, h01, h01.symm]
  have hfac : (Monoid.Coprod.lift (eval (.id G) v) (zpowersPiHom τ hτ)).comp
      (evalGHom (inl.comp inl) p : GX G X →* Monoid.Coprod (GX G X) (Fin 2 → Multiplicative ℤ)) =
        eval (.id G) v := by
    refine GX.ext_hom (fun g => by simp) fun y => ?_
    obtain ⟨i, rfl⟩ | hy := em (∃ i, x i = y)
    · simp only [MonoidHom.coe_comp, MonoidHom.coe_ofClass, coe_evalGHom, Function.comp_apply,
        eval_inr, FreeGroup.lift_apply_of, hx.extend_apply, lift_apply_inr, p]
      fin_cases i <;> simp [τ, a, eq_inv_of_mul_eq_one_right hv₃]
    · simp [p, Function.extend_apply' _ _ _ hy]
  rw [← hfac, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hw, map_one]

/-- Over a fully residually free group `G`, the coordinate group of `x₁² x₂² = 1`, the
non-orientable standard quadratic equation of genus two without coefficients, embeds, over `G`,
in an iterated extension of centralizers of `G`. -/
theorem exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_two
    (hG : IsFullyResiduallyFree G) [Finite X] {S : Standard G X} (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) (hg : S.genus = 2) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {S.toWord}) j), Function.Injective f := by
  by_cases hna : IsMulCommutative G
  · exact exists_ice_embedding_coordGroup_of_isMulCommutative hG.isResiduallyFree _
      ⟨1, one_mem_V_of_constant_eq_one _ hc⟩
  obtain ⟨n, hn, x, inj, rfl⟩ := exists_eq_nonorientable_of_not_isOrientable ho hc
  obtain rfl : n = 2 := by simpa using hg
  exact exists_ice_embedding_coordGroup_sq_mul_sq hG hna inj

/-- Over a fully residually free group `G`, the coordinate group of `x₁² x₂² x₃² = 1`, the
non-orientable standard quadratic equation of genus three without coefficients, embeds, over `G`,
in an iterated extension of centralizers of `G`. -/
theorem exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_three
    (hG : IsFullyResiduallyFree G) [Finite X] {S : Standard G X} (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) (hg : S.genus = 3) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {S.toWord}) j), Function.Injective f := by
  by_cases hna : IsMulCommutative G
  · exact exists_ice_embedding_coordGroup_of_isMulCommutative hG.isResiduallyFree _
      ⟨1, one_mem_V_of_constant_eq_one _ hc⟩
  obtain ⟨n, hn, x, inj, rfl⟩ := exists_eq_nonorientable_of_not_isOrientable ho hc
  obtain rfl : n = 3 := by simpa using hg
  exact exists_ice_embedding_coordGroup_sq_mul_sq_mul_sq hG hna inj

/-! ### Checks over `F(a, b)` -/

/-- Over `F(a, b)`, the equation `x₁² x₂² = 1` in the three variables `x₁`, `x₂`, `x₃`: its
coordinate group `F(a, b) ∗ F(x₁, x₃)` embeds in an iterated extension of centralizers of
`F(a, b)`. -/
example : ∃ (E : Type) (_ : Group E) (j : FreeGroup (Fin 2) →* E) (_ : ICE (FreeGroup (Fin 2)) E j)
    (f : GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup (Fin 2)))
      {(nonorientable 2 two_pos (Fin.castSucc : Fin 2 → Fin 3) (Fin.castSucc_injective 2)).toWord})
      j), Function.Injective f :=
  exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_two
    isFullyResiduallyFree_of_isFreeGroup (not_isOrientable_nonorientable _ _)
    (constant_nonorientable ..) (genus_nonorientable ..)

/-- Over `F(a, b)`, the equation `x₁² x₂² x₃² = 1` is not regular: all its solutions commute, by
Lyndon's theorem. Its coordinate group `F(a, b) ∗ ℤ²` still embeds in an iterated extension of
centralizers of `F(a, b)`. -/
example : ¬(nonorientable (G := FreeGroup (Fin 2)) 3 three_pos id Function.injective_id).IsRegular
      (.id _) ∧
    ∃ (E : Type) (_ : Group E) (j : FreeGroup (Fin 2) →* E) (_ : ICE (FreeGroup (Fin 2)) E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup (Fin 2)))
        {(nonorientable 3 three_pos id Function.injective_id).toWord}) j),
      Function.Injective f :=
  ⟨not_isRegular_nonorientable_of_le_three _ _ le_rfl _,
    exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_three
      isFullyResiduallyFree_of_isFreeGroup (not_isOrientable_nonorientable _ _)
      (constant_nonorientable ..) (genus_nonorientable ..)⟩

end TauCeti.GroupAlgGeom.Quadratic.Standard
