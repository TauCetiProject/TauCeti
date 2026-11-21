/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Centralizer
public import TauCeti.GroupTheory.PushoutI.Centralizer.Basic

/-!
# Centralizers of elliptic elements of an extension of a centralizer

Let `u` be an element of a group `G`, `C = C_G(u)` its centralizer and
`E = G(u, ℤⁿ) = G ∗_C (C × ℤⁿ)` the extension of that centralizer. An element of `E` that is
conjugate into one of the two factors `G` and `C × ℤⁿ` is *elliptic* (it fixes a vertex of the
Bass–Serre tree of the amalgam). This file computes the centralizers of the elliptic elements:

1. an element `g ∈ G` that is not conjugate in `G` into `C` has the same centralizer in `E` as in
   `G`, for every group `G`;
2. if `C` is abelian and malnormal in `G` (as it is for `u ≠ 1` in a CSA group), the centralizer
   in `E` of every nonidentity element of the factor `C × ℤⁿ` is that whole factor.

Every nonidentity elliptic element is conjugate to an element of one of these two kinds, and
centralizers of conjugate elements are conjugate. The remaining elements of `E` are hyperbolic.

For a basis element `a` of a free group `F` and `n = 1`, the centralizer of the new letter `t` in
`F(a, ℤ) = ⟨F, t | [a, t] = 1⟩` is `⟨a, t⟩ ≅ ℤ²`, and the centralizer of another basis
element `b` is still `⟨b⟩`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.centralizer_of_eq_map`: the centralizer of an element of `G`
  not conjugate into `C_G(u)`.
* `TauCeti.LimitGroup.CentralizerExt.centralizer_ofProd_eq_range_ofProd`: the centralizer of a
  nonidentity element of the factor `C_G(u) × ℤⁿ`.
* `TauCeti.LimitGroup.CentralizerExt.centralizer_t_eq_closure_insert`,
  `TauCeti.LimitGroup.CentralizerExt.centralizer_of_of_eq_zpowers`: the two cases in an extension
  of the centralizer of a basis element of a free group.

## References

* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually free
  groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, Lemma 19 (1)–(2).
* A. Myasnikov, V. Remeslennikov, *Exponential groups 2: extensions of centralizers and tensor
  completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996), §6, Lemma 1 (1)–(2).
-/

public section

open Group Subgroup

namespace TauCeti.LimitGroup.CentralizerExt

variable {G : Type*} [Group G] {u : G} {n : ℕ}

/-- **Centralizers of elements of `G` in `G(u, ℤⁿ)`.** The centralizer in `G(u, ℤⁿ)` of an
element `g` of `G` that is not conjugate in `G` into `C_G(u)` is its centralizer in `G`. -/
theorem centralizer_of_eq_map {g : G} (hg : ∀ k : G, k * g * k⁻¹ ∉ centralizer {u}) :
    centralizer {(of g : CentralizerExt u n)} = (centralizer {g}).map of := by
  rw [of_def]
  exact Monoid.PushoutI.centralizer_of_eq_map (centralizerExtMap_injective u n) (i := false)
    fun k hk => hg k (by simpa only [centralizerExtMap_false, range_subtype] using hk)

/-- In `G(u, ℤⁿ)`, if `C_G(u)` is malnormal in `G` and the factor `C_G(u) × ℤⁿ` is abelian, an
element commuting with a nonidentity element `c` of `C_G(u)` lies in that factor. -/
private theorem mem_range_ofProd_of_mem_centralizer (hT : TauCeti.IsTISubgroup (centralizer {u}))
    (hA : ∀ q r : centralizer {u} × (Fin n → Multiplicative ℤ), Commute q r) {c : centralizer {u}}
    (hc : (c : G) ≠ 1) {x : CentralizerExt u n}
    (hx : x ∈ centralizer {(of c : CentralizerExt u n)}) :
    x ∈ (ofProd : _ →* CentralizerExt u n).range := by
  -- Write `x = a * w` with `a` in the factor and `w` a reduced word not starting in it.
  obtain ⟨a, L, hL, hred, hhead, rfl⟩ :=
    Monoid.PushoutI.exists_eq_of_mul_list_prod (φ := centralizerExtMap u n) true x
  rcases L with _ | ⟨⟨_ | _, g⟩, L⟩
  · exact ⟨a, by simp [ofProd_def]⟩
  swap
  · exact absurd rfl (hhead _ rfl)
  -- `w = g * w'` with `g ∈ G ∖ C_G(u)`, and `w'⁻¹ * (g⁻¹ * c * g) * w' = c` is impossible.
  exfalso
  have hcb : Monoid.PushoutI.of (φ := centralizerExtMap u n) false (c : G) =
      Monoid.PushoutI.base _ c := by
    rw [← Monoid.PushoutI.of_apply_eq_base _ false, centralizerExtMap_false, coe_subtype]
  rw [← ofProd_inl] at hx
  have hw := ((hA a (c, 1)).map ofProd).inv_left.mul_left (mem_centralizer_singleton_iff.1 hx)
  rw [ofProd_inl, of_def, hcb, ofProd_def, inv_mul_cancel_left] at hw
  simp only [List.map_cons, List.prod_cons] at hw
  -- `show` retypes the letter `g : CentralizerExtFactor u n false` as an element of `G`.
  have hg : (show G from g) ∉ centralizer {u} := by
    simpa only [centralizerExtMap_false, range_subtype] using hred _ List.mem_cons_self
  refine Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_base
    (centralizerExtMap_injective u n) hL.tail (fun l hl => hred l (List.mem_cons_of_mem _ hl))
    (i := false) (g := (show G from g)⁻¹ * (c : G) * show G from g) ?_
    (fun l hl => ((List.isChain_cons.1 hL).1 l hl).symm) ⟨c, ?_⟩
  · simpa only [centralizerExtMap_false, range_subtype, inv_inv] using
      hT.conj_notMem (inv_mem_iff.not.2 hg) c.property hc
  · simpa [hcb, mul_assoc] using hw.inv_mul_cancel.symm

/-- **Centralizers of elements of the factor `C_G(u) × ℤⁿ`.** If the centralizer `C_G(u)` of `u`
is abelian and malnormal in `G`, then the centralizer in `G(u, ℤⁿ)` of a nonidentity element of
the factor `C_G(u) × ℤⁿ` is that factor. -/
theorem centralizer_ofProd_eq_range_ofProd (hC : IsMulCommutative (centralizer {u}))
    (hT : TauCeti.IsTISubgroup (centralizer {u}))
    {p : centralizer {u} × (Fin n → Multiplicative ℤ)} (hp : p ≠ 1) :
    centralizer {(ofProd p : CentralizerExt u n)} =
      (ofProd : _ →* CentralizerExt u n).range := by
  -- The factor `C_G(u) × ℤⁿ` is abelian.
  have hA (q r : centralizer {u} × (Fin n → Multiplicative ℤ)) : Commute q r :=
    Prod.ext (isMulCommutative_iff.1 hC q.1 r.1) (mul_comm q.2 r.2)
  refine le_antisymm (fun x hx => ?_) ?_
  · by_cases hp2 : p.2 = 1
    · rw [show p = (p.1, 1) from Prod.ext rfl hp2, ofProd_inl] at hx
      exact mem_range_ofProd_of_mem_centralizer hT hA
        (fun h => hp (Prod.ext (Subtype.ext h) hp2)) hx
    · -- `p` lies outside `C_G(u)`, and its conjugates in the abelian factor are `p` itself.
      have hg : ∀ k : centralizer {u} × (Fin n → Multiplicative ℤ),
          k * p * k⁻¹ ∉ (centralizerExtMap u n true).range := by
        rintro k ⟨c, hc⟩
        rw [(hA k p).eq, mul_inv_cancel_right] at hc
        exact hp2 (by rw [← hc, centralizerExtMap_true, MonoidHom.inl_apply])
      rw [ofProd_def] at hx ⊢
      exact map_le_range _ _ <| (Monoid.PushoutI.centralizer_of_eq_map
        (centralizerExtMap_injective u n) (i := true) (g := p) hg).le hx
  · rintro _ ⟨q, rfl⟩
    exact mem_centralizer_singleton_iff.2 ((hA q p).map ofProd).eq

section IsFreeGroup

variable {F : Type*} [Group F] [IsFreeGroup F] {u : F}

/-- For an element `u` of a free group `F` that is not a proper power, the centralizer of each
new letter `tᵢ` in `F(u, ℤⁿ)` is generated by `u` and the new letters, so it is the centralizer
of `u`. For a basis element `a` and `n = 1` it is the subgroup `⟨a, t⟩` of
`⟨F, t | [a, t] = 1⟩`, free abelian of rank two (`centralizerEquivOfNotIsProperPower`). -/
theorem centralizer_t_eq_closure_insert (hu : ¬IsProperPower u) (i : Fin n) :
    centralizer {(t i : CentralizerExt u n)} = closure (insert (of u) (Set.range t)) := by
  have hu1 : u ≠ 1 := fun h => hu (h ▸ IsProperPower.one)
  have hp : ((1, Pi.mulSingle i (.ofAdd 1)) : centralizer {u} × (Fin n → Multiplicative ℤ)) ≠ 1 :=
    fun h => by simpa using congrArg (fun p => p.2 i) h
  rw [← ofProd_mulSingle, centralizer_ofProd_eq_range_ofProd
    (IsFreeGroup.isCSA.centralizer_isMulCommutative hu1)
    (IsFreeGroup.isCSA.centralizer_isTISubgroup u) hp,
    ← centralizer_of_eq_range_ofProd fun _ =>
      IsFreeGroup.isCSA.mem_centralizer_of_conj_mem_centralizer,
    centralizer_of_eq_closure_insert hu]

end IsFreeGroup

/-- For distinct basis elements `a` and `b` of a free group, the centralizer of `b` in the
extension `F(a, ℤⁿ)` of the centralizer of `a` is still the cyclic group `⟨b⟩`. -/
theorem centralizer_of_of_eq_zpowers {α : Type*} {a b : α} (hab : a ≠ b) :
    centralizer {(of (FreeGroup.of b) : CentralizerExt (FreeGroup.of a) n)} =
      zpowers (of (FreeGroup.of b)) := by
  classical
  -- The exponent sum of `b` is `1` on the conjugates of `b` and `0` on the powers of `a`.
  have hg (k : FreeGroup α) : k * FreeGroup.of b * k⁻¹ ∉ centralizer {FreeGroup.of a} := by
    rw [IsFreeGroup.centralizer_singleton_eq_zpowers_self (FreeGroup.not_isProperPower_of a)]
    rintro ⟨m, hm⟩
    simpa [hab, mul_comm] using
      congrArg (FreeGroup.lift fun x => if x = b then Multiplicative.ofAdd (1 : ℤ) else 1) hm.symm
  rw [centralizer_of_eq_map hg,
    IsFreeGroup.centralizer_singleton_eq_zpowers_self (FreeGroup.not_isProperPower_of b),
    MonoidHom.map_zpowers]

end TauCeti.LimitGroup.CentralizerExt
