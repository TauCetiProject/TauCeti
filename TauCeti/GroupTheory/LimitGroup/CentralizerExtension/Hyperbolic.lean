/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Centralizer
public import TauCeti.GroupTheory.PushoutI.Centralizer

/-!
# Centralizers of hyperbolic elements of an extension of a centralizer

Let `u` be an element of a group `G` whose centralizer `C_G(u)` is malnormal in `G`, for instance
any element of a CSA group, and let `G(u, ℤⁿ) = G ∗_{C_G(u)} (C_G(u) × ℤⁿ)` be the extension of
the centralizer of `u`. An element of `G(u, ℤⁿ)` conjugate into neither factor, that is, a
hyperbolic element for the action on the Bass–Serre tree of the amalgam, has cyclic centralizer.
This is the case `‖h‖ ≥ 2` of the description of centralizers in an extension of a centralizer;
the elements conjugate into a factor can have noncyclic centralizers, such as the centralizer
`C_G(u) × ℤⁿ` of `u` (`TauCeti.LimitGroup.CentralizerExt.centralizer_of_eq_range_ofProd`).

For distinct basis elements `a` and `b` of a free group `F`, the element `b * tᵢ` of `F(a, ℤⁿ)` is
hyperbolic, so its centralizer is cyclic, while the centralizer of `a` is free abelian of rank
`n + 1`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.isCyclic_centralizer`: if `C_G(u)` is malnormal in `G`, the
  centralizer in `G(u, ℤⁿ)` of an element conjugate into neither factor is cyclic.
* `TauCeti.LimitGroup.CentralizerExt.isCyclic_centralizer_of_freeGroup_of_mul_t`: the element
  `b * tᵢ` of `F(a, ℤⁿ)` has cyclic centralizer.

## References

* O. Kharlampovich, A. Myasnikov, V. Remeslennikov, D. Serbin, *Subgroups of fully residually free
  groups: algorithmic problems*, Contemp. Math. 360 (2004), §5, Lemma 19 (3).
* J.-P. Serre, *Trees*, Chapter I, §4 and §6.
-/

public section

open Group Subgroup

namespace TauCeti.LimitGroup.CentralizerExt

variable {G : Type*} [Group G] {u : G} {n : ℕ}

/-- If the centralizer of `u` in `G` is malnormal, the centralizer in `G(u, ℤⁿ)` of an element
conjugate into neither factor is cyclic. -/
theorem isCyclic_centralizer (hT : IsTISubgroup (centralizer {u})) {x : CentralizerExt u n}
    (hxG : ∀ y : CentralizerExt u n, y * x * y⁻¹ ∉ (of : G →* CentralizerExt u n).range)
    (hxA : ∀ y : CentralizerExt u n, y * x * y⁻¹ ∉ (ofProd : _ →* CentralizerExt u n).range) :
    IsCyclic (centralizer {x}) := by
  refine Monoid.PushoutI.isCyclic_centralizer (centralizerExtMap_injective u n) (b := false)
    (by rwa [centralizerExtMap_false, range_subtype]) fun i y => ?_
  cases i
  · exact fun h => hxG y (by rwa [of_def])
  · exact fun h => hxA y (by rwa [ofProd_def])

/-- In `F(a, ℤⁿ)` for a free group `F` with distinct basis elements `a` and `b`, the element
`b * tᵢ` has cyclic centralizer. -/
theorem isCyclic_centralizer_of_freeGroup_of_mul_t {α : Type*} {a b : α} (hab : a ≠ b) (i : Fin n) :
    IsCyclic (centralizer {(of (FreeGroup.of b) * t i : CentralizerExt (FreeGroup.of a) n)}) := by
  classical
  set x : CentralizerExt (FreeGroup.of a) n := of (FreeGroup.of b) * t i
  -- A homomorphism to `ℤ` that kills a subgroup and not `x` keeps the conjugates of `x` out of it.
  have key (f : CentralizerExt (FreeGroup.of a) n →* Multiplicative ℤ)
      (S : Subgroup (CentralizerExt (FreeGroup.of a) n)) (hS : S ≤ f.ker) (hx : f x ≠ 1)
      (y : CentralizerExt (FreeGroup.of a) n) : y * x * y⁻¹ ∉ S := fun h =>
    hx (by simpa using hS h)
  refine isCyclic_centralizer (IsFreeGroup.isCSA.centralizer_isTISubgroup _)
    (key (lift 1 (fun _ => .ofAdd 1) (fun _ _ => .all _ _) fun _ _ _ => .all _ _) _ ?_ ?_)
    (key (lift (FreeGroup.lift fun c => if c = b then .ofAdd 1 else 1) 1 (fun _ _ => .all _ _)
      fun _ _ _ => .all _ _) _ ?_ ?_)
  · rintro _ ⟨g, rfl⟩
    simp
  · simp [x]
  · rw [range_ofProd]
    refine sup_le ?_ ((closure_le _).2 ?_)
    · rintro _ ⟨c, hc, rfl⟩
      rw [IsFreeGroup.centralizer_singleton_eq_zpowers_self (FreeGroup.not_isProperPower_of a)]
        at hc
      obtain ⟨k, rfl⟩ := hc
      simp [hab]
    · rintro _ ⟨j, rfl⟩
      simp
  · simp [x]

end TauCeti.LimitGroup.CentralizerExt
