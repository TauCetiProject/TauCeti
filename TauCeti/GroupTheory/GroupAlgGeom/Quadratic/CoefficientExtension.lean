/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAlgGeom.CoefficientExtension
public import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.StandardMap
import TauCeti.GroupTheory.GroupAlgGeom.Quadratic.Surface
import TauCeti.GroupTheory.HNNExtension
import TauCeti.GroupTheory.PushoutI.Basic

/-!
# The group of a standard quadratic equation under an extension of the coefficients

Let `S` be a standard quadratic equation over a torsion-free group `G`, and `G_S = G[X] ⧸ ncl(S)`
its group. Then `S` has a solution in a group containing `G`, so the coefficients embed in `G_S`
(`Quadratic.Standard.systemGroup_coeff_injective`). Hence, for an injective `f : G →* H`, the
homomorphism `SystemGroup.map` from the group of `S` to the group of its image `S.map f` over `H`
is injective (`Quadratic.Standard.systemGroup_map_injective`), by the change of coefficients for
systems whose coefficients embed (`SystemGroup.map_injective`). This is Proposition 2 of
[VAR-I], where `H` is assumed torsion-free as well.

Torsion-freeness of `G` cannot be dropped from either result. Over `G = ℤ/6 = ⟨g⟩`, the equation
`z⁻¹ g³ z g² = 1` makes `g³`, of order dividing `2`, conjugate to `g⁴`, of order dividing `3`, so
both vanish in `G_S`, and so does `g = g³ g⁻²`: the coefficients do not embed. Let `g ∈ A₁₂` have
cycle type `(2, 2, 3, 5)`, so that `G = ⟨g⟩ ≅ ℤ/30`. The equation `z⁻¹ g¹⁵ z g¹⁰ = 1`, which
conjugates an element of order `2` to one of order `3`, has the group `G_S ≅ ℤ/5 ∗ ℤ`. Over the
simple group `H = A₁₂` it kills `H`, so `H_{f(S)} ≅ ℤ` and `G_S → H_{f(S)}` sends `g⁶ ≠ 1`
to `1`.

## Main results

* `TauCeti.GroupAlgGeom.Quadratic.Standard.systemGroup_coeff_injective`: over a torsion-free
  group, `G` embeds in the group of a standard quadratic equation.
* `TauCeti.GroupAlgGeom.Quadratic.Standard.systemGroup_map_injective`: over a torsion-free group,
  the homomorphism `G_S →* H_{f(S)}` induced by an injective `f : G →* H` is injective.

## Implementation notes

The solutions are found in groups containing `G`: amalgamated products in which an element of `G`
is a commutator or a square (`Monoid.PushoutI.exists_injective_commutatorElement_eq`,
`Monoid.PushoutI.exists_injective_pow_eq`), and, for torsion-free `G`, iterated HNN extensions in
which two nontrivial elements of `G` are conjugate
(`HNNExtension.exists_injective_isConj_of_ne_one`) or a given element of `G` is a product of a
conjugate of `c` and a conjugate of `c'`, for nontrivial `c, c' ∈ G`
(`HNNExtension.exists_injective_conj_mul_conj_eq`). Where [VAR-I] compares the decompositions of
`G_S` and `H_{f(S)}` as amalgamated products or HNN extensions over their last atom (Lemma 9),
only the amalgam `H ∗_G G_S` and the embedding of the base group in an HNN extension are used
here.

## References

* [VAR-I] O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I:
  Irreducibility of quadratic equations and Nullstellensatz*, J. Algebra 200 (1998), §1, Lemma 9
  and Proposition 2.
-/

public section

open Function

namespace TauCeti.GroupAlgGeom

universe u

variable {G : Type u} [Group G] {X : Type*}

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

variable {n m : ℕ} {x y : Fin n → X} {z : Fin m → X} {c : Fin m → G} {d : G}

/-- An equation `∏ᵢ [xᵢ, yᵢ] ∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (2) and positive genus over a group `G`
has a solution in a group containing `G`: `x₁`, `y₁` with `[x₁, y₁] = (c₁ ⋯ c_m d)⁻¹`, and `1`
for the other variables. -/
private theorem exists_injective_nonempty_V_orientableCoeff_succ (hnm : 0 < n + 1 + m)
    {x y : Fin (n + 1) → X} (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1)
    (hd : d ≠ 1) : ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧
      (V ι {(orientableCoeff (n + 1) m hnm x y z inj c hc d hd).toWord}).Nonempty := by
  obtain ⟨P, _, ι, hι, a, b, hab⟩ :=
    Monoid.PushoutI.exists_injective_commutatorElement_eq ((List.ofFn c).prod * d)⁻¹
  rw [commutatorElement_def] at hab
  refine ⟨P, _, ι, hι, nonempty_V_orientableCoeff (Fin.cons a⁻¹ 1) (Fin.cons b⁻¹ 1) 1 ?_⟩
  simp only [orientableWord_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Pi.one_apply,
    inv_inv, inv_one, mul_one, List.ofFn_const, List.prod_replicate, one_pow, List.prod_cons]
  simp only [hab, map_inv, map_mul, map_list_prod, List.map_ofFn, Function.comp_def]
  group

variable [IsMulTorsionFree G]

/-- An equation `∏ⱼ zⱼ⁻¹ cⱼ zⱼ d = 1` of type (2) and genus zero over a torsion-free group `G` has
a solution in a group containing `G`: `z₁` conjugating `c₁` to `d⁻¹` if `m = 1`; otherwise `z₁`,
`z₂` with `z₁⁻¹ c₁ z₁ z₂⁻¹ c₂ z₂ = (c₃ ⋯ c_m d)⁻¹`, and `1` for the other variables. -/
private theorem exists_injective_nonempty_V_orientableCoeff_zero (hnm : 0 < 0 + m) {x y : Fin 0 → X}
    (inj : (Sum.elim (Sum.elim x y) z).Injective) (hc : ∀ j, c j ≠ 1) (hd : d ≠ 1) :
    ∃ (P : Type u) (_ : Group P) (ι : G →* P), Injective ι ∧
      (V ι {(orientableCoeff 0 m hnm x y z inj c hc d hd).toWord}).Nonempty := by
  rcases m with _ | _ | m
  · lia
  · obtain ⟨P, _, ι, hι, hk⟩ := HNNExtension.exists_injective_isConj_of_ne_one (hc 0)
      (inv_ne_one.2 hd)
    obtain ⟨k, hk⟩ := isConj_iff.1 hk
    exact ⟨P, _, ι, hι, nonempty_V_orientableCoeff Fin.elim0 Fin.elim0 (fun _ => k⁻¹)
      (by simp [orientableWord_def, hk])⟩
  · obtain ⟨P, _, ι, hι, k, k', hk⟩ := HNNExtension.exists_injective_conj_mul_conj_eq (hc 0)
      (hc 1) ((List.ofFn fun j : Fin m => c j.succ.succ).prod * d)⁻¹
    refine ⟨P, _, ι, hι, nonempty_V_orientableCoeff Fin.elim0 Fin.elim0
      (Fin.cons k⁻¹ (Fin.cons k'⁻¹ 1)) ?_⟩
    calc _ = k * ι (c 0) * k⁻¹ * (k' * ι (c 1) * k'⁻¹) *
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
    exact ⟨G, _, .id G, injective_id, 1, by simp⟩
  | nonorientable n hn x inj =>
    exact ⟨G, _, .id G, injective_id, 1, by simp⟩
  | orientableCoeff n m hnm x y z inj c hc d hd =>
    rcases n with _ | n
    · exact exists_injective_nonempty_V_orientableCoeff_zero hnm inj hc hd
    · exact exists_injective_nonempty_V_orientableCoeff_succ hnm inj hc hd
  | nonorientableCoeff n m hn x z inj c hc d hd =>
    -- `x₁` with `x₁² = (c₁ ⋯ c_m d)⁻¹`, and `1` for the other variables
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one.2 hn
    obtain ⟨P, _, ι, hι, a, ha⟩ :=
      Monoid.PushoutI.exists_injective_pow_eq two_ne_zero ((List.ofFn c).prod * d)⁻¹
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
is torsion-free and `f : G →* H` is injective, the homomorphism `G_S →* H_{f(S)}` induced by `f`
is injective. -/
theorem systemGroup_map_injective {H : Type*} [Group H] [IsMulTorsionFree G] {f : G →* H}
    (hf : Injective f) (S : Standard G X) (hS : ∀ g ∈ S.coeffs, f g ≠ 1)
    (h : Monoid.Coprod.map f (FreeGroup.map id) '' {S.toWord} ⊆
      Subgroup.normalClosure {(S.map f hS).toWord}) :
    Injective (SystemGroup.map f h) :=
  SystemGroup.map_injective hf (systemGroup_coeff_injective S) h <| by
    simpa using Subgroup.subset_normalClosure (Set.mem_singleton _)

end Quadratic.Standard

end TauCeti.GroupAlgGeom
