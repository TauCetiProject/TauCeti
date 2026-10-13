/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Opposite

/-!
# Finite-dimensional preprojective algebras are self-injective

Let `Q` be a finite quiver and `Π = Π_k(Q)` its preprojective algebra over a field `k`. This file
proves that **if `Π` is finite-dimensional, then it is self-injective**, on both sides, over every
field. In particular this applies to the preprojective algebra of every orientation of a finite
simply-laced Dynkin diagram.

## Main results

* `TauCeti.moduleInjective_preprojectiveAlgebra_of_finiteDimensional`: a finite-dimensional
  preprojective algebra is left self-injective.
* `TauCeti.moduleInjective_op_preprojectiveAlgebra_of_finiteDimensional`: it is right
  self-injective.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Section 4, for the self-injectivity of the preprojective
  algebras of Dynkin quivers.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Section 2, for the Koszul complex of a vertex module.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra MulOpposite

universe u v w

variable (k : Type w) [Field k] {Q : Type u} [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

local notation "Π" => preprojectiveAlgebra k Q
local notation "π" => preprojectiveMk k Q

/- Proof outline. No basis, dimension count or Frobenius form is needed: the only input is the
exactness of the Koszul complex of a vertex module at its middle term
(`TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff`). The proof checks Baer's criterion one
vertex at a time. Let `N` be a left ideal of `Π`, let `g : N → Π` be a map of left modules, and let
`m ∈ e_v Π` be an element outside `N` which every arrow `c` leaving `v` moves into `N`. The tuple
`(g (c m))_c` is killed by the second map of the Koszul complex, because
`∑_b ε_b b b* m = ρ_v m = 0`. By exactness at the middle term it is therefore `(c y)_c` for a single
`y ∈ e_v Π`, and `g` extends to `N + Π m` by `m ↦ y`. The extension is well defined because every
element of `Π e_v` is a scalar multiple of `e_v` plus a combination of the paths leaving `v`, and on
`m` the latter act through the arrows `c`.

When `Π` is finite-dimensional such an `m` exists outside every proper left ideal `N`: a path class
outside `N` of maximal length works, since the graded pieces of `Π` vanish in all large degrees. As
the left ideals of `Π` satisfy the ascending chain condition, finitely many such extensions reach
all of `Π`, so `Π` is left self-injective. Right self-injectivity follows by transport along the
isomorphism `Π ≃ Πᵐᵒᵖ` reversing paths (`TauCeti.preprojectiveOpAlgEquiv`). -/

/-- **The value at a new generator.** Let every arrow `c` leaving `v` move `m` into the left ideal
`N`, and let `g : N → Π` be a map of left modules. Then there is one `y ∈ e_v Π` with
`g (c m) = c y` for every such `c`. -/
private theorem exists_value_of_forall_ofArrow_mul_mem (N : Submodule Π Π) (g : N →ₗ[Π] Π)
    {v : Q} {m : Π}
    (hc : ∀ (w : Symmetrify Q) (c : Symmetrify.of.obj v ⟶ w), π (ofArrow c) * m ∈ N) :
    ∃ y, π (doubledVertexIdempotent k v) * y = y ∧ ∀ (w : Symmetrify Q)
      (c : Symmetrify.of.obj v ⟶ w), g ⟨π (ofArrow c) * m, hc w c⟩ = π (ofArrow c) * y := by
  -- The tuple `(g (c m))_c` is killed by the second map of the Koszul complex, since
  -- `∑_b ε_b b b* m = ρ_v m = 0`, so it comes from `e_v Π` by exactness at the middle term.
  have hg_eq {x x' : Π} (hx : x ∈ N) (hx' : x' ∈ N) (h : x = x') : g ⟨x, hx⟩ = g ⟨x', hx'⟩ := by
    subst h; rfl
  have hz (i : Symmetrify Q) (b : i ⟶ Symmetrify.of.obj v) :
      π (vertexIdempotent k i) *
          (doubledArrowSign k b • g ⟨π (ofArrow (Quiver.reverse b)) * m, hc i _⟩) =
        doubledArrowSign k b • g ⟨π (ofArrow (Quiver.reverse b)) * m, hc i _⟩ := by
    rw [mul_smul_comm, ← smul_eq_mul, ← map_smul]
    congr 1
    refine hg_eq _ _ ?_
    rw [smul_eq_mul, ← mul_assoc, ← map_mul, ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]
  have h0 : (∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) • doubledArrowSign k b •
      (⟨π (ofArrow (Quiver.reverse b)) * m, hc i _⟩ : N)) = 0 :=
    Subtype.ext (by
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_smul_of_tower,
        smul_eq_mul, mul_smul_comm, Submodule.coe_zero] using
        sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero k v m)
  have hsum : ∑ i, ∑ b : i ⟶ Symmetrify.of.obj v, π (ofArrow b) *
      (doubledArrowSign k b • g ⟨π (ofArrow (Quiver.reverse b)) * m, hc i _⟩) = 0 := by
    rw [← map_zero g, ← h0]
    simp only [map_sum, map_smul, LinearMap.map_smul_of_tower, smul_eq_mul]
  obtain ⟨y, hy, hyz⟩ := (sum_preprojectiveMk_ofArrow_mul_eq_zero_iff k v hz).1 hsum
  refine ⟨y, hy, fun w c => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b : w ⟶ Symmetrify.of.obj v, Quiver.reverse b = c :=
    ⟨Quiver.reverse c, Quiver.reverse_reverse c⟩
  have h := congrArg (doubledArrowSign k b • ·) (hyz w b)
  simpa only [smul_smul, doubledArrowSign_mul_self, one_smul] using h

/-- **The one-vertex extension is well defined.** Let `m ∈ e_v Π` lie outside the left ideal `N`,
let every arrow `c` leaving `v` move `m` into `N`, and let `y ∈ e_v Π` satisfy `g (c m) = c y`
for all of them. If `n + a m = 0` with `n ∈ N`, then `g n + a y = 0`. -/
private theorem add_mul_eq_zero_of_add_mul_eq_zero (N : Submodule Π Π) (g : N →ₗ[Π] Π) {v : Q}
    {m y : Π} (hm : π (doubledVertexIdempotent k v) * m = m) (hmN : m ∉ N)
    (hc : ∀ (w : Symmetrify Q) (c : Symmetrify.of.obj v ⟶ w), π (ofArrow c) * m ∈ N)
    (hy : π (doubledVertexIdempotent k v) * y = y)
    (hgy : ∀ (w : Symmetrify Q) (c : Symmetrify.of.obj v ⟶ w),
      g ⟨π (ofArrow c) * m, hc w c⟩ = π (ofArrow c) * y)
    (n : N) (a : Π) (hna : (n : Π) + a * m = 0) : g n + a * y = 0 := by
  -- Every element of `Π e_v` is a multiple of `e_v` plus a combination of paths leaving `v`, which
  -- act on `m` through the arrows leaving `v`; the multiple of `e_v` vanishes since `m ∉ N`.
  have hg_eq {x x' : Π} (hx : x ∈ N) (hx' : x' ∈ N) (h : x = x') : g ⟨x, hx⟩ = g ⟨x', hx'⟩ := by
    subst h; rfl
  -- The left ideal of the elements `a` with `a m ∈ N` and `g (a m) = a y`.
  let S : Submodule Π Π :=
    { carrier := {a | ∃ h : a * m ∈ N, g ⟨a * m, h⟩ = a * y}
      add_mem' := by
        rintro a a' ⟨ha, hga⟩ ⟨ha', hga'⟩
        refine ⟨add_mul a a' m ▸ N.add_mem ha ha', ?_⟩
        rw [hg_eq _ (N.add_mem ha ha') (add_mul a a' m), add_mul, ← hga, ← hga']
        exact map_add g ⟨_, ha⟩ ⟨_, ha'⟩
      zero_mem' := ⟨(zero_mul m).symm ▸ N.zero_mem, by
        rw [hg_eq _ N.zero_mem (zero_mul m), zero_mul]
        exact map_zero g⟩
      smul_mem' := by
        rintro c a ⟨ha, hga⟩
        refine ⟨(smul_mul_assoc c a m).symm ▸ N.smul_mem c ha, ?_⟩
        rw [hg_eq _ (N.smul_mem c ha) (smul_mul_assoc c a m), smul_mul_assoc, ← hga]
        exact map_smul g c ⟨_, ha⟩ }
  have hS {a : Π} : a ∈ S ↔ ∃ h : a * m ∈ N, g ⟨a * m, h⟩ = a * y := Iff.rfl
  -- Every class of a path of positive length leaving `v` lies in `S`.
  have hpath {w : Symmetrify Q} (p : Path (Symmetrify.of.obj v) w) (hp : 0 < p.length) :
      π (ofPath ⟨_, _, p⟩) ∈ S := by
    induction p with
    | nil => exact absurd hp (lt_irrefl 0)
    | cons p' c ih =>
      rcases Nat.eq_zero_or_pos p'.length with h0 | hpos
      · obtain rfl := Path.eq_of_length_zero p' h0
        obtain rfl := Path.eq_nil_of_length_zero p' h0
        rw [← Path.comp_toPath_eq_cons, Path.nil_comp, ← ofArrow_eq_ofPath]
        exact hS.2 ⟨hc _ c, hgy _ c⟩
      · rw [← ofArrow_mul_ofPath, map_mul]
        exact S.smul_mem _ (ih hpos)
  -- Every element of `Π e_v` is a multiple of `e_v` plus an element of `S`.
  have hdecomp (a : Π) : ∃ t : k,
      a * π (doubledVertexIdempotent k v) - t • π (doubledVertexIdempotent k v) ∈ S := by
    obtain ⟨f, rfl⟩ := preprojectiveMk_surjective k Q a
    induction f using PathAlgebra.induction_linear with
    | zero => exact ⟨0, by simp only [map_zero, zero_mul, zero_smul, sub_zero, S.zero_mem]⟩
    | add f f' hf hf' =>
      obtain ⟨t, ht⟩ := hf
      obtain ⟨t', ht'⟩ := hf'
      refine ⟨t + t', ?_⟩
      convert S.add_mem ht ht' using 1
      rw [map_add, add_mul, add_smul]
      abel
    | single x c =>
      obtain ⟨u, w, p⟩ := x
      rw [single_eq_smul_ofPath, map_smul, smul_mul_assoc, ← map_mul,
        doubledVertexIdempotent_def]
      by_cases hu : u = Symmetrify.of.obj v
      · subst u
        rw [ofPath_mul_vertexIdempotent]
        rcases Nat.eq_zero_or_pos p.length with h0 | hpos
        · obtain rfl := Path.eq_of_length_zero p h0
          obtain rfl := Path.eq_nil_of_length_zero p h0
          exact ⟨c, by rw [← vertexIdempotent_eq_ofPath, sub_self]; exact S.zero_mem⟩
        · exact ⟨0, by rw [zero_smul, sub_zero]; exact S.smul_of_tower_mem c (hpath p hpos)⟩
      · refine ⟨0, ?_⟩
        rw [ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm hu), map_zero, smul_zero, zero_smul,
          sub_zero]
        exact S.zero_mem
  obtain ⟨t, ht⟩ := hdecomp a
  obtain ⟨hsm, -⟩ := hS.1 ht
  have hamN : a * m ∈ N := by
    rw [eq_neg_of_add_eq_zero_right hna]
    exact N.neg_mem n.2
  have ht0 : t = 0 := by
    by_contra ht0
    apply hmN
    have htm : t • m ∈ N := by
      have ham : a * m = (a * π (doubledVertexIdempotent k v) -
          t • π (doubledVertexIdempotent k v)) * m + t • m := by
        rw [sub_mul, smul_mul_assoc, hm, mul_assoc, hm, sub_add_cancel]
      rw [eq_sub_of_add_eq' ham.symm]
      exact N.sub_mem hamN hsm
    simpa only [smul_smul, inv_mul_cancel₀ ht0, one_smul] using N.smul_of_tower_mem t⁻¹ htm
  rw [ht0, zero_smul, sub_zero] at ht
  obtain ⟨hsm', hgs⟩ := hS.1 ht
  have hame : a * m = a * π (doubledVertexIdempotent k v) * m := by rw [mul_assoc, hm]
  have hn : n = -⟨a * π (doubledVertexIdempotent k v) * m, hsm'⟩ :=
    Subtype.ext ((eq_neg_of_add_eq_zero_left hna).trans (congrArg Neg.neg hame))
  rw [hn, map_neg, hgs, mul_assoc, hy, neg_add_cancel]

/-- **The one-vertex extension step.** Let `m ∈ e_v Π` lie outside the left ideal `N`, and let
every arrow leaving `v` move `m` into `N`. Then every map `N → Π` of left modules extends to
`N + Π m`, sending `m` to the element `y` of `exists_value_of_forall_ofArrow_mul_mem`. -/
private theorem exists_extension_sup_span_singleton (N : Submodule Π Π) (g : N →ₗ[Π] Π) {v : Q}
    {m : Π} (hm : π (doubledVertexIdempotent k v) * m = m) (hmN : m ∉ N)
    (hc : ∀ (w : Symmetrify Q) (c : Symmetrify.of.obj v ⟶ w), π (ofArrow c) * m ∈ N) :
    ∃ g' : ↥(N ⊔ Submodule.span Π {m}) →ₗ[Π] Π,
      ∀ x : N, g' (Submodule.inclusion le_sup_left x) = g x := by
  obtain ⟨y, hy, hgy⟩ := exists_value_of_forall_ofArrow_mul_mem k N g hc
  have hwd := add_mul_eq_zero_of_add_mul_eq_zero k N g hm hmN hc hy hgy
  -- Glue `g` with the map `c m ↦ c y` on `Π m`; the two agree on `N ⊓ Π m` by `hwd`.
  let s : Π →ₗ.[Π] Π := LinearPMap.mkSpanSingleton' m y fun c hcm => by
    simpa only [map_zero, zero_add, RingHom.id_apply, smul_eq_mul] using
      hwd 0 c (by rw [ZeroMemClass.coe_zero, zero_add, ← smul_eq_mul, hcm])
  have hcompat : ∀ (x : (⟨N, g⟩ : Π →ₗ.[Π] Π).domain) (z : s.domain), (x : Π) = z →
      (⟨N, g⟩ : Π →ₗ.[Π] Π) x = s z := by
    rintro x ⟨z, hz⟩ hxz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have h := hwd x (-c) (by rw [hxz, neg_mul, add_neg_eq_zero]; rfl)
    rw [neg_mul, add_neg_eq_zero] at h
    exact h.trans (LinearPMap.mkSpanSingleton'_apply m y _ c hz).symm
  refine ⟨((⟨N, g⟩ : Π →ₗ.[Π] Π).sup s hcompat).toFun, fun x => ?_⟩
  exact ((LinearPMap.left_le_sup _ s hcompat).2 (x := x) rfl).symm

/-- If `Π` is finite-dimensional, then outside every proper left ideal `N` there is an element of
some `e_v Π` which every arrow leaving `v` moves into `N`. -/
private theorem exists_notMem_of_ne_top [FiniteDimensional k Π] {N : Submodule Π Π}
    (hN : N ≠ ⊤) :
    ∃ (v : Q) (m : Π), π (doubledVertexIdempotent k v) * m = m ∧ m ∉ N ∧
      ∀ (w : Symmetrify Q) (c : Symmetrify.of.obj v ⟶ w), π (ofArrow c) * m ∈ N := by
  -- Take the class of a path of maximal length among those whose classes lie outside `N`.
  classical
  let L : Set ℕ := {l | ∃ x : Quiver.TotalPath (Symmetrify Q), x.2.2.length = l ∧ π (ofPath x) ∉ N}
  have hL_fin : L.Finite := by
    refine (WellFoundedGT.finite_ne_bot_of_iSupIndep
      (isInternal_preprojectiveGrade k Q).submodule_iSupIndep).subset ?_
    rintro l ⟨x, rfl, hx⟩ hbot
    have hmem : π (ofPath x) ∈ preprojectiveGrade k Q x.2.2.length := by
      rw [preprojectiveGrade_eq_span_range_ofPath]
      exact Submodule.subset_span ⟨⟨x, rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx (hmem ▸ N.zero_mem)
  have hL_ne : L.Nonempty := by
    by_contra hL
    refine hN (Submodule.eq_top_iff'.2 fun a => ?_)
    obtain ⟨f, rfl⟩ := preprojectiveMk_surjective k Q a
    induction f using PathAlgebra.induction_linear with
    | zero => simpa only [map_zero] using N.zero_mem
    | add f f' hf hf' => simpa only [map_add] using N.add_mem hf hf'
    | single x c =>
      rw [single_eq_smul_ofPath, map_smul]
      refine N.smul_of_tower_mem c (not_not.1 fun hx => hL ⟨_, x, rfl, hx⟩)
  obtain ⟨⟨u, w, p⟩, hp, hpN⟩ := Nat.sSup_mem hL_ne hL_fin.bddAbove
  obtain ⟨v, rfl⟩ : ∃ v : Q, Symmetrify.of.obj v = w := ⟨w, rfl⟩
  refine ⟨v, π (ofPath ⟨u, _, p⟩), ?_, hpN, fun w' c => ?_⟩
  · rw [← map_mul, doubledVertexIdempotent_def]
    exact congrArg π (vertexIdempotent_mul_ofPath p)
  · by_contra hc
    rw [← map_mul, ofArrow_mul_ofPath] at hc
    have hle := le_csSup hL_fin.bddAbove ⟨_, rfl, hc⟩
    have hp' : p.length = sSup L := hp
    simp only [Path.length_cons] at hle
    omega

/-- A finite-dimensional preprojective algebra satisfies Baer's criterion. -/
private theorem moduleBaer_preprojectiveAlgebra [FiniteDimensional k Π] : Module.Baer Π Π := by
  -- Starting from a left ideal, the one-vertex extension step reaches the whole algebra, by the
  -- ascending chain condition on left ideals.
  intro I g
  have : IsNoetherian Π Π := isNoetherian_of_tower k inferInstance
  suffices H : ∀ N : Submodule Π Π, I ≤ N → ∀ h : N →ₗ[Π] Π,
      (∀ x (hxI : x ∈ I) (hxN : x ∈ N), h ⟨x, hxN⟩ = g ⟨x, hxI⟩) →
        ∃ g' : Π →ₗ[Π] Π, ∀ x (hx : x ∈ I), g' x = g ⟨x, hx⟩ from
    H I le_rfl g fun x _ _ => rfl
  intro N
  induction N using WellFoundedGT.induction with
  | _ N ih =>
    intro hIN h hh
    by_cases hN : N = ⊤
    · subst hN
      exact ⟨h ∘ₗ LinearMap.codRestrict ⊤ LinearMap.id fun _ => Submodule.mem_top,
        fun x hx => hh x hx _⟩
    obtain ⟨v, m, hm, hmN, hc⟩ := exists_notMem_of_ne_top k hN
    obtain ⟨h', hh'⟩ := exists_extension_sup_span_singleton k N h hm hmN hc
    have hlt : N < N ⊔ Submodule.span Π {m} :=
      lt_of_le_of_ne le_sup_left fun hEq =>
        hmN (hEq ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self m))
    refine ih _ hlt (hIN.trans le_sup_left) h' fun x hxI hxN => ?_
    have hx : (⟨x, hxN⟩ : ↥(N ⊔ Submodule.span Π {m})) =
        Submodule.inclusion le_sup_left ⟨x, hIN hxI⟩ :=
      Subtype.ext (Submodule.coe_inclusion le_sup_left ⟨x, hIN hxI⟩).symm
    rw [hx, hh', hh]

/-- **A finite-dimensional preprojective algebra is left self-injective**, over every field.
This applies to every orientation of a finite simply-laced Dynkin diagram. -/
theorem moduleInjective_preprojectiveAlgebra_of_finiteDimensional [FiniteDimensional k Π] :
    Module.Injective Π Π :=
  (moduleBaer_preprojectiveAlgebra k).injective

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- **A finite-dimensional preprojective algebra is right self-injective**, over every field.
This applies to every orientation of a finite simply-laced Dynkin diagram. -/
theorem moduleInjective_op_preprojectiveAlgebra_of_finiteDimensional [FiniteDimensional k Π] :
    Module.Injective Πᵐᵒᵖ Π :=
  -- Transport the left regular module along the isomorphism `Π ≃ Πᵐᵒᵖ` reversing paths.
  have := moduleInjective_preprojectiveAlgebra_of_finiteDimensional k (Q := Q)
  .of_ringEquiv (preprojectiveOpAlgEquiv k Q).toRingEquiv
    { (preprojectiveOpAlgEquiv k Q).toRingEquiv.toAddEquiv.trans opAddEquiv.symm with
      map_smul' := fun a x => by
        simp [MulOpposite.smul_eq_mul_unop] }

end TauCeti
