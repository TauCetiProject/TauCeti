/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.HNNExtension.DehnTwist
public import TauCeti.GroupTheory.LimitGroup.CentralizerExtension.Basic

/-!
# The Dehn twist of an extension of a centralizer

The extension `G(u, ℤ) = ⟨G, t | [c, t] = 1, c ∈ C_G(u)⟩` of the centralizer of `u` is an HNN
extension of `G` along the identity of `C_G(u)`, and `u` centralizes `C_G(u)`. The corresponding
Dehn twist is the automorphism of `G(u, ℤ)` fixing `G` and sending `t` to `t * u`. Its `k`-th power
sends `t` to `t * u ^ k`, so that precomposing the retraction `t ↦ u ^ m` onto `G` with it gives
the retraction `t ↦ u ^ (m + k)`: the powers of the twist carry the retraction `t ↦ 1` to all the
retractions `t ↦ u ^ k`.

## Main definitions

* `TauCeti.LimitGroup.CentralizerExt.twist u`: the Dehn twist `t ↦ t * u` of `G(u, ℤ)`.

## Main results

* `TauCeti.LimitGroup.CentralizerExt.twist_zpow_t`: the `k`-th power of the twist sends `t` to
  `t * u ^ k`.
* `TauCeti.LimitGroup.CentralizerExt.retraction_comp_twist_zpow`: the retraction `t ↦ u ^ m`
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
def twist : MulAut (CentralizerExt u 1) :=
  MulAut.congr equivHNNExtension.symm (HNNExtension.dehnTwist (.refl (centralizer {u}))
    ⟨u, mem_centralizer_iff.2 fun _ hc => mem_centralizer_singleton_iff.1 hc⟩)

/-- The powers of the twist fix `G`. -/
@[simp]
theorem twist_zpow_of (k : ℤ) (g : G) : (twist u ^ k) (of g) = of g := by
  rw [twist, ← map_zpow]
  simp

/-- The `k`-th power of the twist sends the new letter `t` to `t * u ^ k`. -/
@[simp]
theorem twist_zpow_t (k : ℤ) (i : Fin 1) : (twist u ^ k) (t i) = t i * of (u ^ k) := by
  rw [twist, ← map_zpow]
  simp [Subsingleton.elim i 0]

/-- The twist fixes `G`. -/
@[simp]
theorem twist_of (g : G) : twist u (of g) = of g := by
  simpa using twist_zpow_of u 1 g

/-- The twist sends the new letter `t` to `t * u`. -/
@[simp]
theorem twist_t (i : Fin 1) : twist u (t i) = t i * of u := by
  simpa using twist_zpow_t u 1 i

/-- The retraction `t ↦ u ^ m` composed with the `k`-th power of the twist is the retraction
`t ↦ u ^ (m + k)`. -/
theorem retraction_comp_twist_zpow (m k : ℤ) :
    (retraction fun _ => m).comp (twist u ^ k).toMonoidHom = retraction fun _ => m + k :=
  hom_ext (by ext; simp) fun i => by simp [zpow_add]

/-- The retraction `t ↦ u ^ m` after the `k`-th power of the twist is the retraction
`t ↦ u ^ (m + k)`. -/
@[simp]
theorem retraction_twist_zpow (m k : ℤ) (x : CentralizerExt u 1) :
    retraction (fun _ => m) ((twist u ^ k) x) = retraction (fun _ => m + k) x :=
  DFunLike.congr_fun (retraction_comp_twist_zpow u m k) x

end TauCeti.LimitGroup.CentralizerExt
