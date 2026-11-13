/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardMap
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Surface
import TauCeti.GroupTheory.HNNExtension
import TauCeti.GroupTheory.PushoutI.Basic

/-!
# The group of a standard quadratic equation under an extension of the coefficients

Let `S` be a system of equations over a group `G` in the variables `X`, and `G_S = G[X] ⧸ ncl(S)`
its group. An injective homomorphism `f : G →* H` induces `G[X] →* H[X]`, and the image `f(S)` of
`S` is a system over `H`. If `G` embeds in `G_S`, the induced homomorphism `G_S →* H_{f(S)}` is
injective (`SystemGroup.comap_normalClosure_image`); indeed `H_{f(S)}` is the amalgamated product
`H ∗_G G_S`.

Over a torsion-free group `G`, every standard quadratic equation `S` has a solution in a group
containing `G`, so the coefficients embed in `G_S`
(`Quadratic.Standard.systemGroup_coeff_injective`). Hence the group of `S` embeds in the group of
its image `S.map f` over `H` (`Quadratic.Standard.exists_injective_systemGroup_map`). This is
Proposition 2 of [VAR-I], where `H` is assumed torsion-free as well. Torsion-freeness of `G` cannot
be dropped: over `G = ℤ/6 = ⟨g⟩`, the equation `z⁻¹ g³ z g² = 1` makes `g³`, of order dividing `2`,
conjugate to `g⁴`, of order dividing `3`, so both vanish in `G_S`, and so does `g = g³ g⁻²`.

## Main results

* `TauCeti.GroupAlgGeom.SystemGroup.comap_normalClosure_image`: if `f` is injective and `G` embeds
  in `G_S`, a word whose image lies in the normal closure of `f(S)` lies in that of `S`.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.systemGroup_coeff_injective`: over a torsion-free
  group, `G` embeds in the group of a standard quadratic equation.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.exists_injective_systemGroup_map`: over a torsion-free
  group, the homomorphism `G_S →* H_{f(S)}` induced by an injective `f : G →* H` is injective.

## Implementation notes

The solutions are found in iterated HNN extensions of `G`
(`HNNExtension.exists_injective_isConj_of_orderOf_eq`): where `g ≠ 1` is conjugate to `g²`, it is a
commutator and a square, and two such extensions make any element of `G` a product of a conjugate
of `c` and a conjugate of `c'`, for nontrivial `c, c' ∈ G`. Where [VAR-I] compares the
decompositions of `G_S` and `H_{f(S)}` as amalgamated products or HNN extensions over their last
atom (Lemma 9), only the amalgam `H ∗_G G_S` and the embedding of the base group in an HNN
extension are used here.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1, Lemma 9
  and Proposition 2.
-/

public section

open Function Monoid.Coprod Subgroup

namespace TauCeti.GroupAlgGeom

universe u

variable {G : Type u} [Group G] {X : Type*}

namespace SystemGroup

/-- **Change of coefficients.** Let `f : G →* H` be injective and `S` a system of equations over
`G` such that `G` embeds in `G_S`. A word of `G[X]` whose image under `f` lies in the normal
closure of the image of `S` lies in the normal closure of `S`; that is, the homomorphism
`G_S →* H_{f(S)}` induced by `f` is injective. -/
theorem comap_normalClosure_image {H : Type*} [Group H] {f : G →* H} (hf : Injective f)
    {S : Set (GX G X)} (hS : Injective (coeff S)) :
    (normalClosure (Monoid.Coprod.map f (FreeGroup.map id) '' S)).comap
      (Monoid.Coprod.map f (FreeGroup.map id)) = normalClosure S := by
  set F : GX G X →* GX H X := Monoid.Coprod.map f (FreeGroup.map id)
  refine le_antisymm (fun w hw => ?_) (comap_normalClosure_image_ge S F)
  -- `H_{F(S)}` maps to the amalgam `P` of `H` and `G_S` over `G`, in which `G_S` embeds
  obtain ⟨P, _, α, β, -, hβ, hαβ⟩ := Monoid.PushoutI.exists_injective_comp_eq_comp hf hS
  let θ : GX H X →* P :=
    Monoid.Coprod.lift α (FreeGroup.lift fun x => β (inr (FreeGroup.of x) : GX G X))
  have hθ : θ.comp F = β.comp (QuotientGroup.mk' (normalClosure S)) := by
    ext g
    · simpa [θ, F] using DFunLike.congr_fun hαβ g
    · simp [θ, F]
  have hker : normalClosure (F '' S) ≤ θ.ker := by
    refine normalClosure_le_normal ?_
    rintro _ ⟨s, hs, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← MonoidHom.comp_apply, hθ]
    simp [(QuotientGroup.eq_one_iff s).2 (subset_normalClosure hs)]
  rw [← QuotientGroup.eq_one_iff, ← map_eq_one_iff β hβ]
  simpa [MonoidHom.mem_ker.1 (hker hw)] using (DFunLike.congr_fun hθ w).symm

end SystemGroup

namespace Quadratic.Standard

open SurfaceGroup

section Solutions

variable {P : Type*} [Group P] {ι : G →* P} {n m : ℕ} {x y : Fin n → X} {z : Fin m → X}
  {c : Fin m → G} {d : G}

/-- Values `α`, `β`, `τ` of the variables `xᵢ`, `yᵢ`, `zⱼ` at which the left side of an equation of
type (2) vanishes give a solution. -/
private theorem nonempty_V_orientableCoeff {hnm : 0 < n + m}
    {inj : (Sum.elim (Sum.elim x y) z).Injective} {hc : ∀ j, c j ≠ 1} {hd : d ≠ 1} (α β : Fin n → P)
    (τ : Fin m → P) (h : orientableWord α β (fun j => (τ j)⁻¹ * ι (c j) * τ j) * ι d = 1) :
    (V ι {(orientableCoeff n m hnm x y z inj c hc d hd).toWord}).Nonempty := by
  set v : X → P := Function.extend (Sum.elim (Sum.elim x y) z) (Sum.elim (Sum.elim α β) τ) 1
  have hx (i : Fin n) : v (x i) = α i := inj.extend_apply _ _ (Sum.inl (Sum.inl i))
  have hy (i : Fin n) : v (y i) = β i := inj.extend_apply _ _ (Sum.inl (Sum.inr i))
  have hz (j : Fin m) : v (z j) = τ j := inj.extend_apply _ _ (Sum.inr j)
  refine ⟨v, ?_⟩
  rw [mem_V, Set.forall_mem_singleton, eval_toWord_orientableCoeff, orientableWord_snoc]
  simpa only [hx, hy, hz] using h

/-- Values `κ`, `τ` of the variables `xᵢ`, `zⱼ` at which the left side of an equation of type (4)
vanishes give a solution. -/
private theorem nonempty_V_nonorientableCoeff {x : Fin n → X} {hn : 0 < n}
    {inj : (Sum.elim x z).Injective} {hc : ∀ j, c j ≠ 1} {hd : d ≠ 1} (κ : Fin n → P)
    (τ : Fin m → P) (h : nonorientableWord κ (fun j => (τ j)⁻¹ * ι (c j) * τ j) * ι d = 1) :
    (V ι {(nonorientableCoeff n m hn x z inj c hc d hd).toWord}).Nonempty := by
  set v : X → P := Function.extend (Sum.elim x z) (Sum.elim κ τ) 1
  have hx (i : Fin n) : v (x i) = κ i := inj.extend_apply _ _ (Sum.inl i)
  have hz (j : Fin m) : v (z j) = τ j := inj.extend_apply _ _ (Sum.inr j)
  refine ⟨v, ?_⟩
  rw [mem_V, Set.forall_mem_singleton, eval_toWord_nonorientableCoeff, nonorientableWord_snoc]
  simpa only [hx, hz] using h

end Solutions

section Overgroups

variable [IsMulTorsionFree G]

/-- In a torsion-free group, all nontrivial elements have the same (infinite) order. -/
private theorem orderOf_eq_orderOf {a b : G} (ha : a ≠ 1) (hb : b ≠ 1) : orderOf a = orderOf b := by
  rw [orderOf_eq_zero_iff.2 (not_isOfFinOrder_of_isMulTorsionFree ha),
    orderOf_eq_zero_iff.2 (not_isOfFinOrder_of_isMulTorsionFree hb)]

/-- Two nontrivial elements of a torsion-free group are conjugate in a group containing it. -/
private theorem exists_conj_eq {c g : G} (hc : c ≠ 1) (hg : g ≠ 1) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧ ∃ k : P, k⁻¹ * ι c * k = ι g := by
  obtain ⟨P, _, ι, hι, hk⟩ :=
    HNNExtension.exists_injective_isConj_of_orderOf_eq (orderOf_eq_orderOf hc hg)
  obtain ⟨k, hk⟩ := isConj_iff.1 hk
  exact ⟨P, _, ι, hι, k⁻¹, by simpa [mul_assoc] using hk⟩

/-- A nontrivial element `g` of a torsion-free group is conjugate to `g²` in a group containing
it. -/
private theorem exists_conj_eq_sq {g : G} (hg : g ≠ 1) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧ ∃ k : P, k⁻¹ * ι g * k = ι g ^ 2 := by
  simpa using exists_conj_eq hg ((pow_eq_one_iff_left two_ne_zero).not.2 hg)

/-- Every element of a torsion-free group is a commutator `a⁻¹ b⁻¹ a b` in a group containing it:
if `k⁻¹ g k = g²` then `g⁻¹ k⁻¹ g k = g`. -/
private theorem exists_commutator_eq (g : G) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧
      ∃ a b : P, a⁻¹ * b⁻¹ * a * b = ι g := by
  rcases eq_or_ne g 1 with rfl | hg
  · exact ⟨G, _, .id G, injective_id, 1, 1, by simp⟩
  obtain ⟨P, _, ι, hι, k, hk⟩ := exists_conj_eq_sq hg
  refine ⟨P, _, ι, hι, ι g, k, ?_⟩
  calc (ι g)⁻¹ * k⁻¹ * ι g * k = (ι g)⁻¹ * (k⁻¹ * ι g * k) := by group
    _ = ι g := by rw [hk]; group

/-- Every element of a torsion-free group is a square in a group containing it: if `k⁻¹ g k = g²`
then `(k g k⁻¹)² = g`. -/
private theorem exists_sq_eq (g : G) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧ ∃ a : P, a ^ 2 = ι g := by
  rcases eq_or_ne g 1 with rfl | hg
  · exact ⟨G, _, .id G, injective_id, 1, by simp⟩
  obtain ⟨P, _, ι, hι, k, hk⟩ := exists_conj_eq_sq hg
  refine ⟨P, _, ι, hι, k * ι g * k⁻¹, ?_⟩
  calc (k * ι g * k⁻¹) ^ 2 = k * ι g ^ 2 * k⁻¹ := by rw [sq, sq]; group
    _ = ι g := by rw [← hk]; group

/-- For nontrivial elements `c`, `c'` of a torsion-free group, every element `h` is the product of
a conjugate of `c` and a conjugate of `c'` in a group containing it. -/
private theorem exists_conj_mul_conj_eq {c c' : G} (hc : c ≠ 1) (hc' : c' ≠ 1) (h : G) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧
      ∃ k k' : P, k⁻¹ * ι c * k * (k'⁻¹ * ι c' * k') = ι h := by
  rcases eq_or_ne c h with rfl | hh
  · -- `h = c`: conjugate `c` to `c²` and then `c'` to `c⁻¹`
    obtain ⟨P₁, _, ι₁, hι₁, k₁, hk₁⟩ := exists_conj_eq_sq hc
    obtain ⟨P, _, ι₂, hι₂, hk₂⟩ := HNNExtension.exists_injective_isConj_of_orderOf_eq
      (a := ι₁ c') (b := ι₁ c⁻¹) (by
        rw [orderOf_injective ι₁ hι₁, orderOf_injective ι₁ hι₁]
        exact orderOf_eq_orderOf hc' (inv_ne_one.2 hc))
    obtain ⟨k₂, hk₂⟩ := isConj_iff.1 hk₂
    refine ⟨P, _, ι₂.comp ι₁, hι₂.comp hι₁, ι₂ k₁, k₂⁻¹, ?_⟩
    calc (ι₂ k₁)⁻¹ * (ι₂.comp ι₁) c * ι₂ k₁ * (k₂⁻¹⁻¹ * (ι₂.comp ι₁) c' * k₂⁻¹)
        = ι₂ (k₁⁻¹ * ι₁ c * k₁) * (k₂ * ι₂ (ι₁ c') * k₂⁻¹) := by simp [mul_assoc]
      _ = (ι₂.comp ι₁) c := by rw [hk₁, hk₂]; simp [sq, mul_assoc]
  · obtain ⟨P, _, ι, hι, k, hk⟩ := exists_conj_eq hc' (inv_mul_eq_one.not.2 hh)
    exact ⟨P, _, ι, hι, 1, k, by simp [hk]⟩

variable {n m : ℕ} {x y : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

/-- An equation `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (2) and positive genus over a
torsion-free group `G` has a solution in a group containing `G`: `x₁`, `y₁` with
`[x₁, y₁] = (c₁ ⋯ c_m d)⁻¹`, and `1` for the other variables. -/
private theorem exists_injective_nonempty_V_orientableCoeff_succ (hnm : 0 < n + 1 + m)
    {x y : Fin (n + 1) → X} (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) : ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧
      (V ι {(orientableCoeff (n + 1) m hnm x y z inj c hc d hd).toWord}).Nonempty := by
  obtain ⟨P, _, ι, hι, a, b, hab⟩ := exists_commutator_eq ((List.ofFn c).prod * d)⁻¹
  refine ⟨P, _, ι, hι, nonempty_V_orientableCoeff (Fin.cons a 1) (Fin.cons b 1) 1 ?_⟩
  simp only [orientableWord_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Pi.one_apply,
    inv_one, mul_one, List.ofFn_const, List.prod_replicate, one_pow, List.prod_cons]
  simp only [hab, map_inv, map_mul, map_list_prod, List.map_ofFn, Function.comp_def]
  group

/-- An equation `∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (2) and genus zero over a torsion-free group `G` has
a solution in a group containing `G`: `z₁` conjugating `c₁` to `d⁻¹` if `m = 1`; otherwise `z₁`,
`z₂` with `z₁⁻¹ c₁ z₁ z₂⁻¹ c₂ z₂ = (c₃ ⋯ c_m d)⁻¹`, and `1` for the other variables. -/
private theorem exists_injective_nonempty_V_orientableCoeff_zero (hnm : 0 < 0 + m) {x y : Fin 0 → X}
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧
      (V ι {(orientableCoeff 0 m hnm x y z inj c hc d hd).toWord}).Nonempty := by
  rcases m with _ | _ | m
  · lia
  · obtain ⟨P, _, ι, hι, k, hk⟩ := exists_conj_eq (hc 0) (inv_ne_one.2 hd)
    exact ⟨P, _, ι, hι, nonempty_V_orientableCoeff Fin.elim0 Fin.elim0 (fun _ => k)
      (by simp [orientableWord_def, hk])⟩
  · obtain ⟨P, _, ι, hι, k, k', hk⟩ := exists_conj_mul_conj_eq (hc 0) (hc 1)
      ((List.ofFn fun j : Fin m => c j.succ.succ).prod * d)⁻¹
    refine ⟨P, _, ι, hι, nonempty_V_orientableCoeff Fin.elim0 Fin.elim0
      (Fin.cons k (Fin.cons k' 1)) ?_⟩
    calc _ = k⁻¹ * ι (c 0) * k * (k'⁻¹ * ι (c 1) * k') *
          ((List.ofFn fun i => ι (c i.succ.succ)).prod * ι d) := by
            simp [orientableWord_def, List.ofFn_succ, mul_assoc]
      _ = 1 := by
        rw [hk]
        simp only [map_inv, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
          inv_mul_cancel]

/-- A standard quadratic equation over a torsion-free group `G` has a solution in a group
containing `G`. -/
private theorem exists_injective_nonempty_V (S : Standard G X) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧ (V ι {S.toWord}).Nonempty := by
  cases S with
  | orientable n hn x y inj =>
    exact ⟨G, _, .id G, injective_id, 1, by simp [orientableWord_def]⟩
  | nonorientable n hn x inj =>
    exact ⟨G, _, .id G, injective_id, 1, by simp [nonorientableWord_def]⟩
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    rcases n with _ | n
    · exact exists_injective_nonempty_V_orientableCoeff_zero hnm inj hc hd
    · exact exists_injective_nonempty_V_orientableCoeff_succ hnm inj hc hd
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    -- `x₁` with `x₁² = (c₁ ⋯ c_m d)⁻¹`, and `1` for the other variables
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.2 hn
    obtain ⟨P, _, ι, hι, a, ha⟩ := exists_sq_eq ((List.ofFn c).prod * d)⁻¹
    exact ⟨P, _, ι, hι, nonempty_V_nonorientableCoeff (Fin.cons a 1) 1 (by
      simp [nonorientableWord_def, List.ofFn_succ, ha, map_list_prod, List.map_ofFn,
        Function.comp_def, mul_assoc])⟩

end Overgroups

/-- **The coefficients embed in the group of a standard quadratic equation.** Over a torsion-free
group `G`, the coefficient homomorphism `G →* G_S` of a standard quadratic equation `S` is
injective. -/
theorem systemGroup_coeff_injective [IsMulTorsionFree G] (S : Standard G X) :
    Injective (SystemGroup.coeff (G := G) {S.toWord}) := by
  obtain ⟨P, _, ι, hι, hV⟩ := exists_injective_nonempty_V S
  exact SystemGroup.coeff_injective hι hV

/-- **The group of a standard quadratic equation under an extension of the coefficients.** If `G`
is torsion-free and `f : G →* H` is injective, the homomorphism `G_S → H_{f(S)}` induced by `f`
is injective. -/
theorem exists_injective_systemGroup_map {H : Type*} [Group H] [IsMulTorsionFree G] {f : G →* H}
    (hf : Function.Injective f) (S : Standard G X) :
    ∃ F : SystemGroup G {S.toWord} →* SystemGroup H
        {(S.map f fun _ hg => (map_ne_one_iff f hf).2 (ne_one_of_mem_coeffs hg)).toWord},
      Function.Injective F ∧ ∀ w : GX G X, F (QuotientGroup.mk w) =
        QuotientGroup.mk (Monoid.Coprod.map f (FreeGroup.map id) w) := by
  have h := SystemGroup.comap_normalClosure_image hf (systemGroup_coeff_injective S)
  rw [Set.image_singleton] at h
  rw [toWord_map]
  exact ⟨QuotientGroup.map _ _ _ h.ge, (QuotientGroup.map_injective_iff _ _ _ h.ge).2 h.le,
    fun _ => rfl⟩

end Quadratic.Standard

end TauCeti.GroupAlgGeom
