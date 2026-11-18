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
import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Transport
import TauCeti.GroupTheory.NoncommPiCoprod

/-!
# Coordinate groups of `x₁² x₂² = 1` and `x₁² x₂² x₃² = 1`

Let `G` be a fully residually free group and `X` a finite set of variables. The non-orientable
standard quadratic equations `x₁² x₂² = 1` and `x₁² x₂² x₃² = 1` without coefficients have only
commutative solutions in `G`, and their radicals are larger than the normal closures of the
equations:

* `G` has unique roots, so every solution of `x₁² x₂² = 1` has `x₂ = x₁⁻¹`. The radical is the
  normal closure of `x₁ x₂`, the kernel of the substitution `x₂ ↦ x₁⁻¹`, and the coordinate group
  is `G ∗ F(X ∖ {x₂})`.
* By Lyndon's theorem in free groups, `G` satisfies Vaught's condition
  (`TauCeti.LimitGroup.IsResiduallyFree.isVaught`); it is also torsion-free, so every solution of
  `x₁² x₂² x₃² = 1` consists of pairwise commuting `x₁`, `x₂`, `x₃` with `x₁ x₂ x₃ = 1`. The
  radical is the kernel of the map to `G[X] ∗ ℤ²` sending `x₁`, `x₂` to the generators `a₁`, `a₂`
  of `ℤ²` and `x₃` to `(a₁ a₂)⁻¹`, and the coordinate group is `G ∗ ℤ² ∗ F(X ∖ {x₁, x₂, x₃})`.

In both cases the coordinate group embeds, over `G`, in an iterated extension of centralizers of
`G`; this embedding, not the description of the radical, is what is stated here. For nonabelian
`G`, the free `G`-group `G[X]` embeds in one extension of a centralizer of `G` and `G[X] ∗ ℤ²` in
one more (`TauCeti.LimitGroup.exists_ice_embedding_GX`,
`TauCeti.LimitGroup.exists_ice_embedding_coprod_pi`); the kernel of a `G`-homomorphism into an
iterated extension of centralizers, which is discriminated by `G`, is its own radical. For abelian
`G` the coordinate group is `G × ℤᵏ`
(`TauCeti.GroupAlgGeom.exists_ice_embedding_coordGroup_of_isMulCommutative`).

These are the cases (4) and (5) of the radicals of consistent standard quadratic equations over a
freely discriminated group, whose printed formulas in [IFT] omit the relations `x₁ x₂ = 1` and
`x₁ x₂ x₃ = 1`, and two of the low-genus cases of the embedding theorem of [VAR-I].

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

-- The common last step: if `σ : G[X] →* L` over `G` kills `S` and every solution of `S` factors
-- through `σ`, then `ker σ` is the radical of `S`, and the coordinate group of `S` embeds in `L`
-- and in every iterated extension of centralizers in which `L` embeds.
private theorem exists_ice_embedding_coordGroup_of_factor (hG : IsFullyResiduallyFree G)
    {L : Type*} [Group L] {l : G →* L}
    (hL : ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j) (f : GHom l j),
      Function.Injective f)
    (σ : GHom (inl : G →* GX G X) l) {S : Set (GX G X)} (hS : S ⊆ (σ : GX G X →* L).ker)
    (hfac : ∀ v ∈ V (.id G) S, ∃ ψ : L →* G, ψ.comp σ = eval (.id G) v) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) S) j), Function.Injective f := by
  obtain ⟨E, _, j, c, e, he⟩ := hL
  have hRad : (σ : GX G X →* L).ker ≤ Rad (.id G) S := fun w hw => mem_Rad.2 fun v hv => by
    obtain ⟨ψ, hψ⟩ := hfac v hv
    rw [← hψ, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hw, map_one]
  -- `E` is discriminated, hence separated, by `G`, and `G[X] ⧸ ker σ` embeds in it through `e`.
  obtain ⟨f, hf, -⟩ :=
    ((c.isDiscriminatedBy hG).isSeparatedBy).exists_injective_gHom_coordGroup_of_injective
      (hS.trans (subset_Rad _)) hRad
      ⟨(e : L →* E).comp (QuotientGroup.kerLift _), fun g => by simp [GX.quotientCoeff_apply]⟩
      (he.comp (QuotientGroup.kerLift_injective _))
  exact ⟨E, _, j, c, f, hf⟩

-- Over a nonabelian fully residually free group, every solution of `x₁² x₂² = 1` factors through
-- the substitution `x₂ ↦ x₁⁻¹` of `G[X]`, which embeds in an extension of a centralizer.
private theorem exists_ice_embedding_coordGroup_sq_mul_sq (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) [Countable X] {x : Fin 2 → X} (hx : x.Injective) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G)
        {(inr (FreeGroup.of (x 0)) : GX G X) ^ 2 * inr (FreeGroup.of (x 1)) ^ 2}) j),
      Function.Injective f := by
  classical
  have := hG.isResiduallyFree.hasUniqueRoots
  let p : X → GX G X :=
    Function.update (fun y => inr (FreeGroup.of y)) (x 1) (inr (FreeGroup.of (x 0)))⁻¹
  refine exists_ice_embedding_coordGroup_of_factor hG (exists_ice_embedding_GX hG hna X)
    (evalGHom inl p) (by simp [p, hx.ne zero_ne_one]) fun v hv => ⟨eval (.id G) v, ?_⟩
  -- By unique roots `v x₁ = (v x₂)⁻¹`, so `v` factors through the substitution.
  have hv₁ : v (x 0) = (v (x 1))⁻¹ := by
    simpa [mul_eq_one_iff_eq_inv, ← inv_pow, (pow_left_injective two_ne_zero).eq_iff] using
      (mem_V.1 hv) _ rfl
  refine GX.ext_hom (fun g => by simp) fun y => ?_
  by_cases hy : y = x 1 <;> simp [p, hy, hv₁]

-- Over a nonabelian fully residually free group `G`, `G[X] ∗ ℤ²` embeds, over `G`, in an iterated
-- extension of centralizers of `G`.
private theorem exists_ice_embedding_GX_coprod_pi (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) [Countable X] :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom ((inl : GX G X →* Monoid.Coprod (GX G X) (Fin 2 → Multiplicative ℤ)).comp inl)
        j), Function.Injective f := by
  obtain ⟨E, _, j, c, e, he⟩ := exists_ice_embedding_GX hG hna X
  have hK : ¬IsMulCommutative (GX G X) := fun _ => hna <| .of_comm fun a b =>
    inl_injective (N := FreeGroup X) <| by rw [map_mul, map_mul, mul_comm']
  obtain ⟨E', _, j', c', g, hg⟩ :=
    exists_ice_embedding_coprod_pi ((c.isFullyResiduallyFree hG).of_injective he) hK 2
  exact ICE.exists_embedding_comp hG c e he c' g hg

-- Over a nonabelian fully residually free group, every solution of `x₁² x₂² x₃² = 1` factors
-- through the map `G[X] →* G[X] ∗ ℤ²` sending `x₁`, `x₂` to the generators `a₁`, `a₂` of `ℤ²` and
-- `x₃` to `(a₁ a₂)⁻¹`.
private theorem exists_ice_embedding_coordGroup_sq_mul_sq_mul_sq (hG : IsFullyResiduallyFree G)
    (hna : ¬IsMulCommutative G) [Countable X] {x : Fin 3 → X} (hx : x.Injective) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G)
        {(inr (FreeGroup.of (x 0)) : GX G X) ^ 2 * inr (FreeGroup.of (x 1)) ^ 2 *
          inr (FreeGroup.of (x 2)) ^ 2}) j),
      Function.Injective f := by
  classical
  have := hG.isResiduallyFree.isMulTorsionFree
  let a : Fin 2 → Fin 2 → Multiplicative ℤ := fun i => Pi.mulSingle i (.ofAdd 1)
  let p : X → Monoid.Coprod (GX G X) (Fin 2 → Multiplicative ℤ) := Function.extend x
    (fun i => inr (![a 0, a 1, (a 0 * a 1)⁻¹] i)) fun y => inl (inr (FreeGroup.of y))
  -- `x₁² x₂² x₃²` goes to `a₁² a₂² (a₁ a₂)⁻² = 1` in `ℤ²`.
  have ha : a 0 ^ 2 * a 1 ^ 2 * ((a 0 * a 1)⁻¹) ^ 2 = 1 := by rw [inv_pow, mul_pow, mul_inv_cancel]
  have hS := congrArg (inr : _ →* Monoid.Coprod (GX G X) (Fin 2 → Multiplicative ℤ)) ha
  refine exists_ice_embedding_coordGroup_of_factor hG (exists_ice_embedding_GX_coprod_pi hG hna)
    (evalGHom _ p) (by simpa [p, hx.extend_apply] using hS) fun v hv => ?_
  -- By Vaught's condition and torsion-freeness `v x₁`, `v x₂`, `v x₃` commute and have product `1`.
  have h3 : v (x 0) ^ 2 * v (x 1) ^ 2 * v (x 2) ^ 2 = 1 := by simpa using (mem_V.1 hv) _ rfl
  obtain ⟨h01, h02, h12⟩ := (Group.isVaught_iff G).1 hG.isResiduallyFree.isVaught _ _ _ h3
  have hv₃ : v (x 2) = (v (x 0) * v (x 1))⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ((pow_eq_one_iff_left two_ne_zero).1 ?_)
    simpa [(h02.mul_left h12).mul_pow, h01.mul_pow] using h3
  let τ : Fin 2 → G := ![v (x 0), v (x 1)]
  have hτ : ∀ i j, Commute (τ i) (τ j) := by simp [τ, Fin.forall_fin_two, h01, h01.symm]
  refine ⟨Monoid.Coprod.lift (eval (.id G) v) (zpowersPiHom τ hτ),
    GX.ext_hom (fun g => by simp) fun y => ?_⟩
  by_cases hy : ∃ i, x i = y
  · obtain ⟨i, rfl⟩ := hy
    fin_cases i <;> simp [p, hx.extend_apply, τ, a, hv₃]
  · simp [p, Function.extend_apply' _ _ _ hy]

/-- Over a fully residually free group `G`, the coordinate group of `x₁² x₂² = 1`, the
non-orientable standard quadratic equation of genus two without coefficients, embeds, over `G`,
in an iterated extension of centralizers of `G`. -/
theorem exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_two
    (hG : IsFullyResiduallyFree G) [Finite X] {S : Standard G X} (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) (hg : S.genus = 2) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {S.toWord}) j), Function.Injective f := by
  cases S with
  | orientable => exact absurd (isOrientable_orientable ..) ho
  | orientableCoeff => exact absurd (isOrientable_orientableCoeff ..) ho
  | nonorientableCoeff _ _ _ _ _ _ _ _ _ hd => exact absurd (by simpa using hc) hd
  | nonorientable n hn x inj =>
    obtain rfl : n = 2 := by simpa using hg
    by_cases hna : IsMulCommutative G
    · exact exists_ice_embedding_coordGroup_of_isMulCommutative hG.isResiduallyFree _
        ⟨1, by simp [toWord_def, atoms_nonorientable]⟩
    · have hw : (nonorientable (G := G) 2 hn x inj).toWord =
          inr (FreeGroup.of (x 0)) ^ 2 * inr (FreeGroup.of (x 1)) ^ 2 := by
        simp [toWord_def, atoms_nonorientable, List.ofFn_succ]
      rw [hw]
      exact exists_ice_embedding_coordGroup_sq_mul_sq hG hna inj

/-- Over a fully residually free group `G`, the coordinate group of `x₁² x₂² x₃² = 1`, the
non-orientable standard quadratic equation of genus three without coefficients, embeds, over `G`,
in an iterated extension of centralizers of `G`. -/
theorem exists_ice_embedding_coordGroup_of_not_isOrientable_of_genus_eq_three
    (hG : IsFullyResiduallyFree G) [Finite X] {S : Standard G X} (ho : ¬S.IsOrientable)
    (hc : S.constant = 1) (hg : S.genus = 3) :
    ∃ (E : Type u) (_ : Group E) (j : G →* E) (_ : ICE G E j)
      (f : GHom (CoordGroup.coeff (MonoidHom.id G) {S.toWord}) j), Function.Injective f := by
  cases S with
  | orientable => exact absurd (isOrientable_orientable ..) ho
  | orientableCoeff => exact absurd (isOrientable_orientableCoeff ..) ho
  | nonorientableCoeff _ _ _ _ _ _ _ _ _ hd => exact absurd (by simpa using hc) hd
  | nonorientable n hn x inj =>
    obtain rfl : n = 3 := by simpa using hg
    by_cases hna : IsMulCommutative G
    · exact exists_ice_embedding_coordGroup_of_isMulCommutative hG.isResiduallyFree _
        ⟨1, by simp [toWord_def, atoms_nonorientable]⟩
    · have hw : (nonorientable (G := G) 3 hn x inj).toWord =
          inr (FreeGroup.of (x 0)) ^ 2 * inr (FreeGroup.of (x 1)) ^ 2 *
            inr (FreeGroup.of (x 2)) ^ 2 := by
        simp [toWord_def, atoms_nonorientable, List.ofFn_succ, mul_assoc]
      rw [hw]
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
