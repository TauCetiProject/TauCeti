/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HNNExtension.DehnTwist
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The Dehn twist of an extension of a centralizer

The extension `G(u, ℤ) = ⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩` of the centralizer of `u` is an HNN
extension of `G` along the identity of `C_G(u)`, and `u` centralizes `C_G(u)`. The corresponding
Dehn twist is the automorphism of `G(u, ℤ)` fixing `G` and sending `t` to `t * u`. Its `k`-th power
sends `t` to `t * u ^ k`, so that precomposing the retraction `t ↦ u ^ m` onto `G` with it gives
the retraction `t ↦ u ^ (m + k)`: the powers of the twist carry the retraction `t ↦ 1` to all the
retractions `t ↦ u ^ k`.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.dehnTwist u`: the Dehn twist `t ↦ t * u` of `G(u, ℤ)`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.dehnTwist_zpow_apply_t`: the `k`-th power of the twist sends
  `t` to `t * u ^ k`.
* `TauCeti.LimitGroup.CentralizerExt.dehnTwist_eq_one_iff`: the twist is trivial exactly when
  `u = 1`.
* `TauCeti.LimitGroup.CentralizerExt.dehnTwist_mem_fixingSubgroup`,
  `TauCeti.LimitGroup.CentralizerExt.zpowers_dehnTwist_le_fixingSubgroup`: the twist and its
  powers fix `G`.
* `TauCeti.LimitGroup.CentralizerExt.retraction_comp_dehnTwist_zpow`: the retraction `t ↦ u ^ m`
  composed with the `k`-th power of the twist is the retraction `t ↦ u ^ (m + k)`.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.5 (extensions of centralizers) and §5.6 (canonical automorphisms).
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, §5.1.4 (twists).
-/

public section

namespace TauCeti.LimitGroup.CentralizerExt

open Subgroup

universe u

variable {G : Type u} [Group G] (u : G)

/-- The Dehn twist of `G(u, ℤ)`: the automorphism fixing `G` and sending the new letter `t` to
`t * u`. -/
def dehnTwist : MulAut (CentralizerExt u 1) :=
  MulAut.congr equivHNNExtension.symm (HNNExtension.dehnTwist (.refl (centralizer {u}))
    ⟨u, mem_centralizer_iff.2 fun _ hc => mem_centralizer_singleton_iff.1 hc⟩)

/-- The powers of the twist fix `G`. -/
@[simp]
theorem dehnTwist_zpow_apply_of (k : ℤ) (g : G) : (dehnTwist u ^ k) (of g) = of g := by
  rw [dehnTwist, ← map_zpow]
  simp

/-- The `k`-th power of the twist sends the new letter `t` to `t * u ^ k`. -/
@[simp]
theorem dehnTwist_zpow_apply_t (k : ℤ) (i : Fin 1) :
    (dehnTwist u ^ k) (t i) = t i * of (u ^ k) := by
  rw [dehnTwist, ← map_zpow]
  simp [Subsingleton.elim i 0]

/-- The natural powers of the twist fix `G`. -/
@[simp]
theorem dehnTwist_pow_apply_of (n : ℕ) (g : G) : (dehnTwist u ^ n) (of g) = of g := by
  simpa using dehnTwist_zpow_apply_of u n g

/-- The `n`-th power of the twist sends the new letter `t` to `t * u ^ n`. -/
@[simp]
theorem dehnTwist_pow_apply_t (n : ℕ) (i : Fin 1) :
    (dehnTwist u ^ n) (t i) = t i * of (u ^ n) := by
  simpa using dehnTwist_zpow_apply_t u n i

/-- The twist fixes `G`. -/
@[simp]
theorem dehnTwist_of (g : G) : dehnTwist u (of g) = of g := by
  simpa using dehnTwist_zpow_apply_of u 1 g

/-- The twist sends the new letter `t` to `t * u`. -/
@[simp]
theorem dehnTwist_t (i : Fin 1) : dehnTwist u (t i) = t i * of u := by
  simpa using dehnTwist_zpow_apply_t u 1 i

/-- The inverse of the twist fixes `G`. -/
@[simp]
theorem dehnTwist_symm_apply_of (g : G) : (dehnTwist u).symm (of g) = of g := by
  simpa using dehnTwist_zpow_apply_of u (-1) g

/-- The inverse of the twist sends the new letter `t` to `t * u⁻¹`. -/
@[simp]
theorem dehnTwist_symm_apply_t (i : Fin 1) : (dehnTwist u).symm (t i) = t i * of u⁻¹ := by
  simpa using dehnTwist_zpow_apply_t u (-1) i

/-- The twist is trivial exactly when `u = 1`. -/
@[simp]
theorem dehnTwist_eq_one_iff : dehnTwist u = 1 ↔ u = 1 := by
  rw [dehnTwist, MulEquiv.map_eq_one_iff, HNNExtension.dehnTwist_eq_one_iff, Subgroup.mk_eq_one]

/-- The twist of the extension of the centralizer of `1` is trivial. -/
@[simp]
theorem dehnTwist_one : dehnTwist (1 : G) = 1 :=
  (dehnTwist_eq_one_iff 1).2 rfl

/-- The twist fixes `G`. -/
@[simp]
theorem dehnTwist_mem_fixingSubgroup :
    dehnTwist u ∈ fixingSubgroup (MulAut (CentralizerExt u 1))
      (Set.range (of : G →* CentralizerExt u 1)) :=
  (mem_fixingSubgroup_iff _).2 fun _ ⟨g, hg⟩ => hg ▸ dehnTwist_of u g

/-- The powers of the twist fix `G`. -/
theorem zpowers_dehnTwist_le_fixingSubgroup :
    zpowers (dehnTwist u) ≤ fixingSubgroup (MulAut (CentralizerExt u 1))
      (Set.range (of : G →* CentralizerExt u 1)) :=
  zpowers_le.2 (dehnTwist_mem_fixingSubgroup u)

/-- The retraction `t ↦ u ^ m` composed with the `k`-th power of the twist is the retraction
`t ↦ u ^ (m + k)`. -/
theorem retraction_comp_dehnTwist_zpow (m : Fin 1 → ℤ) (k : ℤ) :
    (retraction m).comp (dehnTwist u ^ k).toMonoidHom = retraction fun i => m i + k :=
  hom_ext (by ext; simp) fun i => by simp [zpow_add]

/-- The retraction `t ↦ u ^ m` after the `k`-th power of the twist is the retraction
`t ↦ u ^ (m + k)`. -/
@[simp]
theorem retraction_dehnTwist_zpow (m : Fin 1 → ℤ) (k : ℤ) (x : CentralizerExt u 1) :
    retraction m ((dehnTwist u ^ k) x) = retraction (fun i => m i + k) x :=
  DFunLike.congr_fun (retraction_comp_dehnTwist_zpow u m k) x

/-- The retraction `t ↦ u ^ m` after the `n`-th power of the twist is the retraction
`t ↦ u ^ (m + n)`. -/
@[simp]
theorem retraction_dehnTwist_pow (m : Fin 1 → ℤ) (n : ℕ) (x : CentralizerExt u 1) :
    retraction m ((dehnTwist u ^ n) x) = retraction (fun i => m i + n) x := by
  simpa using retraction_dehnTwist_zpow u m n x

/-- The retraction `t ↦ u ^ m` after the twist is the retraction `t ↦ u ^ (m + 1)`. -/
@[simp]
theorem retraction_dehnTwist (m : Fin 1 → ℤ) (x : CentralizerExt u 1) :
    retraction m (dehnTwist u x) = retraction (fun i => m i + 1) x := by
  simpa using retraction_dehnTwist_zpow u m 1 x

/-- The retraction `t ↦ u ^ m` after the inverse of the twist is the retraction
`t ↦ u ^ (m - 1)`. -/
@[simp]
theorem retraction_dehnTwist_symm (m : Fin 1 → ℤ) (x : CentralizerExt u 1) :
    retraction m ((dehnTwist u).symm x) = retraction (fun i => m i - 1) x := by
  simpa [← sub_eq_add_neg] using retraction_dehnTwist_zpow u m (-1) x

end TauCeti.LimitGroup.CentralizerExt
