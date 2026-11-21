/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import TauCeti.GroupTheory.PushoutI.Centralizer.Hyperbolic
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.GroupTheory.FreeGroup.CSA

/-!
# Centralizers of hyperbolic elements of an extension of a centralizer

Let `u` be an element of a group `G` whose centralizer `C_G(u)` is malnormal in `G`, for instance
any element of a CSA group, and let `G(u, ℤⁿ) = G ∗_{C_G(u)} (C_G(u) × ℤⁿ)` be the extension of
the centralizer of `u`. An element of `G(u, ℤⁿ)` conjugate into neither factor, that is, a
hyperbolic element for the action on the Bass–Serre tree of the amalgam, has cyclic centralizer.
This is the case `‖h‖ ≥ 2` of the description of centralizers in an extension of a centralizer,
where `‖h‖` is the least number of letters of a reduced form of a conjugate of `h`; the elements
with `‖h‖ ≤ 1` are those conjugate into a factor. These elliptic elements can have noncyclic
centralizers, such as the centralizer `C_G(u) × ℤⁿ` of `u`
(`TauCeti.LimitGroup.CentralizerExt.centralizer_of_eq_range_ofProd`).
`TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Elliptic` computes the centralizers of two
kinds of elliptic elements: of an element of `G` not conjugate in `G` into `C_G(u)`, for every
group `G`, and of a nonidentity element of the factor `C_G(u) × ℤⁿ`, when moreover `C_G(u)` is
abelian (as it is for `u ≠ 1` in a CSA group).

For distinct basis elements `a` and `b` of a free group `F`, the element `b * tᵢ` of `F(a, ℤⁿ)` is
hyperbolic, so its centralizer is cyclic, while the centralizer of `a` is free abelian of rank
`n + 1`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.isCyclic_centralizer`: if `C_G(u)` is malnormal in `G`, the
  centralizer in `G(u, ℤⁿ)` of an element conjugate into neither factor is cyclic.
* `TauCeti.LimitGroup.CentralizerExt.conj_of_mul_t_notMem_range_of`: no conjugate of `g * tᵢ`
  lies in `G`.
* `TauCeti.LimitGroup.CentralizerExt.conj_of_mul_t_notMem_range_ofProd`: in `F(a, ℤⁿ)`, no
  conjugate of `b * tᵢ` lies in `C_F(a) × ℤⁿ`; so `b * tᵢ` is conjugate into neither factor.
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

/-- For every `g ∈ G`, no conjugate of `g * tᵢ` in `G(u, ℤⁿ)` lies in `G`. -/
theorem conj_of_mul_t_notMem_range_of (g : G) (i : Fin n) (y : CentralizerExt u n) :
    y * (of g * t i) * y⁻¹ ∉ (of : G →* CentralizerExt u n).range :=
  -- The homomorphism to `ℤ` killing `G` and sending every `tⱼ` to `1` does not kill `g * tᵢ`.
  (lift (K := Multiplicative ℤ) 1 (fun _ => .ofAdd 1) (fun _ _ => .all _ _)
    fun _ _ _ => .all _ _).conj_notMem_of_le_ker (by rintro _ ⟨g, rfl⟩; simp) (by simp) y

/-- In `F(a, ℤⁿ)` for a free group `F` with distinct basis elements `a` and `b`, no conjugate of
`b * tᵢ` lies in the factor `C_F(a) × ℤⁿ = ⟨a⟩ × ℤⁿ`. -/
theorem conj_of_mul_t_notMem_range_ofProd {α : Type*} {a b : α} (hab : a ≠ b) (i : Fin n)
    (y : CentralizerExt (FreeGroup.of a) n) :
    y * (of (FreeGroup.of b) * t i) * y⁻¹ ∉
      (ofProd : _ →* CentralizerExt (FreeGroup.of a) n).range := by
  classical
  -- The homomorphism to `ℤ` sending `b` to `1` and the other basis elements and every `tⱼ` to `0`
  -- kills `⟨a⟩ × ℤⁿ` but not `b * tᵢ`.
  refine (lift (K := Multiplicative ℤ) (FreeGroup.lift fun c => if c = b then .ofAdd 1 else 1) 1
    (fun _ _ => .all _ _) fun _ _ _ => .all _ _).conj_notMem_of_le_ker ?_ (by simp) y
  rintro _ ⟨⟨⟨c, hc⟩, v⟩, rfl⟩
  rw [MonoidHom.mem_ker, lift_ofProd, zpowersPiHom_apply_eq_prod]
  -- Every `tⱼ` maps to `1`, and `c ∈ C_F(a) = ⟨a⟩` maps to `1` since `a ≠ b`.
  rw [IsFreeGroup.centralizer_singleton_eq_zpowers_self (FreeGroup.not_isProperPower_of a)] at hc
  obtain ⟨k, rfl⟩ := hc
  simp [hab]

/-- In `F(a, ℤⁿ)` for a free group `F` with distinct basis elements `a` and `b`, the element
`b * tᵢ` has cyclic centralizer. -/
theorem isCyclic_centralizer_of_freeGroup_of_mul_t {α : Type*} {a b : α} (hab : a ≠ b) (i : Fin n) :
    IsCyclic (centralizer {(of (FreeGroup.of b) * t i : CentralizerExt (FreeGroup.of a) n)}) :=
  isCyclic_centralizer (IsFreeGroup.isCSA.centralizer_isTISubgroup _)
    (conj_of_mul_t_notMem_range_of _ i) (conj_of_mul_t_notMem_range_ofProd hab i)

end TauCeti.LimitGroup.CentralizerExt
