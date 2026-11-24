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

/-!
# Coordinate groups of `x₁² x₂² = 1` and `x₁² x₂² x₃² = 1`

Let `G` be a fully residually free group and `X` a countable set of variables. The non-orientable
standard quadratic equations `x₁² x₂² = 1` and `x₁² x₂² x₃² = 1` without coefficients have only
commutative solutions in `G`:

* `G` has unique roots, so every solution of `x₁² x₂² = 1` has `x₂ = x₁⁻¹`.
* By Lyndon's theorem in free groups, `G` satisfies Vaught's condition
  (`TauCeti.LimitGroup.IsResiduallyFree.isVaught`), so every solution of `x₁² x₂² x₃² = 1`
  consists of pairwise commuting `x₁`, `x₂`, `x₃`; `G` is also torsion-free, so `x₁ x₂ x₃ = 1`
  (`TauCeti.mul_mul_eq_one_of_sq_mul_sq_mul_sq_eq_one_of_commute`).

So the radicals of both equations are larger than their normal closures. If `G` is not abelian,
they are described by these relations:

* the radical of `x₁² x₂² = 1` is the normal closure of `x₁ x₂`, the kernel of the substitution
  `x₂ ↦ x₁⁻¹`, and its coordinate group is `G ∗ F(X ∖ {x₂})`;
* the radical of `x₁² x₂² x₃² = 1` is the kernel of the map to `G[X] ∗ ℤ²` sending `x₁`, `x₂` to
  the generators `a₁`, `a₂` of `ℤ²` and `x₃` to `(a₁ a₂)⁻¹`, and its coordinate group is
  `G ∗ ℤ² ∗ F(X ∖ {x₁, x₂, x₃})`.

If `G` is abelian, both radicals also contain the commutator subgroup of `G[X]`, and for finite
`X` both coordinate groups are of the form `G × ℤᵏ`.

If `G` is nonabelian or `X` is finite, the coordinate group embeds, over `G`, in an iterated
extension of centralizers of `G`; this embedding, not the description of the radical, is what is
stated here. For nonabelian `G`, the free `G`-group `G[X]` embeds in one extension of a
centralizer of `G` and `G[X] ∗ ℤ²` in one more (`TauCeti.LimitGroup.exists_ice_embedding_GX`,
`TauCeti.LimitGroup.exists_ice_embedding_coprod_pi_of_exists_ice_embedding`). Every solution
factors through the maps to these groups described above, so their kernels lie in the radicals.
Iterated extensions of centralizers of `G` are discriminated, hence separated, by `G`
(`TauCeti.LimitGroup.ICE.isDiscriminatedBy`), so the coordinate groups embed with them
(`TauCeti.GroupAlgGeom.IsSeparatedBy.exists_injective_gHom_coordGroup_of_ker_le_Rad`). For
abelian `G` and finite `X` the embedding is
`TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_isMulCommutative`.

These are the cases (4) and (5) of the radicals of consistent standard quadratic equations over a
freely discriminated group, whose printed formulas in [IFT] omit the relations `x₁ x₂ = 1` and
`x₁ x₂ x₃ = 1` (and, for abelian `G`, the commutators with the coefficients), and two of the
low-genus cases of the embedding theorem of [VAR-I].

## Main results

* `Standard.exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_two`: for a finite set
  of variables `X`, the coordinate group of `x₁² x₂² = 1` embeds, over `G`, in an iterated
  extension of centralizers of `G`.
* `Standard.exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_three`: the same for
  `x₁² x₂² x₃² = 1`, again for finite `X`.
* `Standard.exists_ice_embedding_coordGroup_nonorientable_two_of_not_isMulCommutative`,
  `Standard.exists_ice_embedding_coordGroup_nonorientable_three_of_not_isMulCommutative`: the same
  embeddings for nonabelian `G` and a countable, possibly infinite, set of variables `X`.

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

/-- Over a nonabelian fully residually free group `G`, the coordinate group of `x₁² x₂² = 1` in a
countable set of variables embeds, over `G`, in an iterated extension of centralizers of `G`. -/
theorem exists_ice_embedding_coordGroup_nonorientable_two_of_not_isMulCommutative
    (hG : IsFullyResiduallyFree G) (hna : ¬IsMulCommutative G) [Countable X] {x : Fin 2 → X}
    (hx : x.Injective) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {(nonorientable 2 two_pos x hx).toWord}) j),
      Function.Injective f := by
  classical
  have hword : (nonorientable (G := G) 2 two_pos x hx).toWord =
      inr (FreeGroup.of (x 0)) ^ 2 * inr (FreeGroup.of (x 1)) ^ 2 := by
    simp [toWord_def, List.ofFn_succ]
  rw [hword]
  -- Every solution factors through the substitution `x₂ ↦ x₁⁻¹` of `G[X]`.
  have := hG.isResiduallyFree.hasUniqueRoots
  let p : X → GX G X :=
    Function.update (fun y => inr (FreeGroup.of y)) (x 1) (inr (FreeGroup.of (x 0)))⁻¹
  obtain ⟨E, _, j, c, e, he⟩ := exists_ice_embedding_GX hG hna X
  refine ((c.isDiscriminatedBy hG).isSeparatedBy.exists_injective_gHom_coordGroup_of_ker_le_Rad
    (evalGHom inl p) (by simp [p, hx.ne zero_ne_one]) (fun w hw => mem_Rad.2 fun v hv => ?_) e
    he).elim fun f hf => ⟨E, _, j, c, f, hf.1⟩
  -- By unique roots `v x₁ v x₂ = 1`, so `v` factors through the substitution.
  rw [V_pow_mul_pow two_ne_zero] at hv
  have hv₁ : v (x 0) = (v (x 1))⁻¹ := eq_inv_of_mul_eq_one_left (by simpa using (mem_V.1 hv) _ rfl)
  have hfac : (eval (.id G) v).comp (eval inl p) = eval (.id G) v := by
    rw [eval_comp_eval]
    congr 1
    funext y
    by_cases hy : y = x 1 <;> simp [p, hy, hv₁]
  have hw' : eval inl p w = 1 := by simpa using hw
  rw [← hfac, MonoidHom.comp_apply, hw', map_one]

/-- Over a nonabelian fully residually free group `G`, the coordinate group of
`x₁² x₂² x₃² = 1` in a countable set of variables embeds, over `G`, in an iterated extension of
centralizers of `G`. -/
theorem exists_ice_embedding_coordGroup_nonorientable_three_of_not_isMulCommutative
    (hG : IsFullyResiduallyFree G) (hna : ¬IsMulCommutative G) [Countable X] {x : Fin 3 → X}
    (hx : x.Injective) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {(nonorientable 3 three_pos x hx).toWord}) j),
      Function.Injective f := by
  have hword : (nonorientable (G := G) 3 three_pos x hx).toWord = inr (FreeGroup.of (x 0)) ^ 2 *
      inr (FreeGroup.of (x 1)) ^ 2 * inr (FreeGroup.of (x 2)) ^ 2 := by
    simp [toWord_def, List.ofFn_succ, mul_assoc]
  rw [hword]
  -- Every solution factors through the map `G[X] →* G[X] ∗ ℤ²` sending `x₁`, `x₂` to the
  -- generators `a₁`, `a₂` of `ℤ²` and `x₃` to `(a₁ a₂)⁻¹`.
  let a : Fin 2 → Fin 2 → Multiplicative ℤ := fun i => Pi.mulSingle i (.ofAdd 1)
  let p : X → Monoid.Coprod (GX G X) (Fin 2 → Multiplicative ℤ) := Function.extend x
    (fun i => inr (![a 0, a 1, (a 0 * a 1)⁻¹] i)) fun y => inl (inr (FreeGroup.of y))
  -- `x₁² x₂² x₃²` goes to `a₁² a₂² (a₁ a₂)⁻² = 1` in `ℤ²`.
  have ha : a 0 ^ 2 * a 1 ^ 2 * ((a 0 * a 1)⁻¹) ^ 2 = 1 := by rw [inv_pow, mul_pow, mul_inv_cancel]
  obtain ⟨E, _, j, c, e, he⟩ := exists_ice_embedding_coprod_pi_of_exists_ice_embedding hG hna
    (exists_ice_embedding_GX hG hna X) 2
  refine ((c.isDiscriminatedBy hG).isSeparatedBy.exists_injective_gHom_coordGroup_of_ker_le_Rad
    (evalGHom _ p)
    (by simpa [p, hx.extend_apply] using congrArg (inr : _ →* Monoid.Coprod (GX G X) _) ha)
    (fun w hw => mem_Rad.2 fun v hv => ?_) e he).elim fun f hf => ⟨E, _, j, c, f, hf.1⟩
  -- By Vaught's condition `v x₁`, `v x₂`, `v x₃` commute pairwise, and by torsion-freeness
  -- `v x₁ v x₂ v x₃ = 1`.
  have := hG.isResiduallyFree.isMulTorsionFree
  have hsq : v (x 0) ^ 2 * v (x 1) ^ 2 * v (x 2) ^ 2 = 1 := by simpa using (mem_V.1 hv) _ rfl
  obtain ⟨h01, h02, h12⟩ := (Group.isVaught_iff G).1 hG.isResiduallyFree.isVaught _ _ _ hsq
  have hv₃ := mul_mul_eq_one_of_sq_mul_sq_mul_sq_eq_one_of_commute h01 h02 h12 hsq
  let τ : Fin 2 → G := ![v (x 0), v (x 1)]
  have hτ : ∀ i j, Commute (τ i) (τ j) := by simp [τ, Fin.forall_fin_two, h01, h01.symm]
  let φ := Monoid.Coprod.lift (eval (.id G) v) (zpowersPiHom τ hτ)
  have hfac : φ.comp (eval (inl.comp inl) p) = eval (.id G) v := by
    rw [MonoidHom.comp_eval]
    congr 1
    · ext g
      simp [φ]
    · funext y
      obtain ⟨i, rfl⟩ | hy := em (∃ i, x i = y)
      · fin_cases i <;> simp [φ, p, τ, a, hx.extend_apply, eq_inv_of_mul_eq_one_right hv₃]
      · simp [φ, p, Function.extend_apply' _ _ _ hy]
  have hw' : eval (inl.comp inl) p w = 1 := by simpa using hw
  rw [← hfac, MonoidHom.comp_apply, hw', map_one]

/-- Over a fully residually free group `G`, the coordinate group of `x₁² x₂² = 1`, the
non-orientable standard quadratic equation of genus two without coefficients, in a finite set of
variables `X` embeds, over `G`, in an iterated extension of centralizers of `G`. For nonabelian `G`
and countable `X`, see `exists_ice_embedding_coordGroup_nonorientable_two_of_not_isMulCommutative`.
-/
theorem exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_two
    (hG : IsFullyResiduallyFree G) [Finite X] {S : Standard G X} (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) (hg : S.genus = 2) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {S.toWord}) j), Function.Injective f := by
  obtain ⟨n, hn, x, inj, rfl⟩ := exists_eq_nonorientable_of_not_isOrientable ho hc
  by_cases hna : IsMulCommutative G
  · exact exists_ice_embedding_coordGroup_of_isMulCommutative hG.isResiduallyFree _ ⟨1, by simp⟩
  obtain rfl : n = 2 := by simpa using hg
  exact exists_ice_embedding_coordGroup_nonorientable_two_of_not_isMulCommutative hG hna inj

/-- Over a fully residually free group `G`, the coordinate group of `x₁² x₂² x₃² = 1`, the
non-orientable standard quadratic equation of genus three without coefficients, in a finite set of
variables `X` embeds, over `G`, in an iterated extension of centralizers of `G`. For nonabelian `G`
and countable `X`, see
`exists_ice_embedding_coordGroup_nonorientable_three_of_not_isMulCommutative`. -/
theorem exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_three
    (hG : IsFullyResiduallyFree G) [Finite X] {S : Standard G X} (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) (hg : S.genus = 3) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {S.toWord}) j), Function.Injective f := by
  obtain ⟨n, hn, x, inj, rfl⟩ := exists_eq_nonorientable_of_not_isOrientable ho hc
  by_cases hna : IsMulCommutative G
  · exact exists_ice_embedding_coordGroup_of_isMulCommutative hG.isResiduallyFree _ ⟨1, by simp⟩
  obtain rfl : n = 3 := by simpa using hg
  exact exists_ice_embedding_coordGroup_nonorientable_three_of_not_isMulCommutative hG hna inj

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

/-- Over `F(a, b)`, the equation `x₀² x₁² = 1` in the variables `x₀, x₁, x₂, …` indexed by `ℕ`: its
coordinate group `F(a, b) ∗ F(x₀, x₂, x₃, …)` embeds in an iterated extension of centralizers of
`F(a, b)`. -/
example : ∃ (E : Type) (_ : Group E) (j : FreeGroup (Fin 2) →* E) (_ : ICE (FreeGroup (Fin 2)) E j)
    (f : GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup (Fin 2)))
      {(nonorientable 2 two_pos (Fin.val : Fin 2 → ℕ) Fin.val_injective).toWord}) j),
    Function.Injective f :=
  exists_ice_embedding_coordGroup_nonorientable_two_of_not_isMulCommutative
    isFullyResiduallyFree_of_isFreeGroup
    (FreeGroup.isMulCommutative_iff_subsingleton.not.2 (not_subsingleton (Fin 2))) _

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
