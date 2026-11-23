/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.HaagerupProperty.Basic
import TauCeti.GroupTheory.PositiveDefinite.Basic

/-!
# The Haagerup property and subgroups of finite index

A discrete group has the Haagerup property as soon as one of its subgroups of finite index has it.
Choose representatives `s x` of the cosets `x ∈ G ⧸ H`. Each approximating positive-definite
function `φ` on `H` induces the positive-definite function
`g ↦ [G : H]⁻¹ ∑_{x ∈ G ⧸ H} φ₀ ((s (g • x))⁻¹ * g * s x)` on `G`, with `φ₀` the extension of `φ`
by zero (`TauCeti.inducedFun`). It equals `1` at the identity and vanishes at infinity. It is
within `ε` of `1` on a finite set `F ⊆ G` once `φ` is within `ε` of `1` on the finitely many
elements `(s (g • x))⁻¹ * g * s x` of `H` with `g ∈ F`. Together with the passage to subgroups,
this shows that the Haagerup property only depends on a subgroup of finite index.

## Main declarations

* `TauCeti.HasHaagerupProperty.of_finiteIndex`: a group with a subgroup of finite index having the
  Haagerup property has the Haagerup property.
* `TauCeti.hasHaagerupProperty_iff_of_finiteIndex`: a group has the Haagerup property if and only
  if a given subgroup of finite index does.

## References

* P.-A. Cherix, M. Cowling, P. Jolissaint, P. Julg and A. Valette, *Groups with the Haagerup
  property*, Progress in Mathematics 197, Birkhäuser (2001), Proposition 6.1.5.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §16.1.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- A group has the Haagerup property if one of its subgroups of finite index has it. -/
theorem HasHaagerupProperty.of_finiteIndex {H : Subgroup G} [H.FiniteIndex]
    (hH : HasHaagerupProperty H) : HasHaagerupProperty G := by
  classical
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite _
  let s : G ⧸ H → G := Quotient.out
  have hs (x : G ⧸ H) : (s x : G ⧸ H) = x := QuotientGroup.out_eq' x
  refine hasHaagerupProperty_iff.mpr fun F ε hε ↦ ?_
  -- The finitely many elements of `H` at which the induced function samples `φ` on `F`.
  let F' : Finset H := (F ×ˢ Finset.univ).image fun p : G × G ⧸ H ↦
    ⟨(s (p.1 • p.2))⁻¹ * p.1 * s p.2, inv_mul_mul_mem_of_section hs p.1 p.2⟩
  obtain ⟨φ, hpd, h1, hlim, hF'⟩ := hasHaagerupProperty_iff.mp hH F' ε hε
  refine ⟨inducedFun s φ, posSemidef_inducedFun s hpd, by rw [inducedFun_one, h1],
    tendsto_inducedFun_cofinite s hlim, fun g hg ↦ norm_inducedFun_sub_one_lt hs fun x ↦ ?_⟩
  exact hF' _ (Finset.mem_image.mpr ⟨(g, x), Finset.mem_product.mpr ⟨hg, Finset.mem_univ x⟩, rfl⟩)

/-- A group has the Haagerup property if and only if a given subgroup of finite index has it. -/
theorem hasHaagerupProperty_iff_of_finiteIndex (H : Subgroup G) [H.FiniteIndex] :
    HasHaagerupProperty G ↔ HasHaagerupProperty H :=
  ⟨fun hG ↦ hG.subgroup H, HasHaagerupProperty.of_finiteIndex⟩

end TauCeti
