/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Snake
public import TauCeti.RepresentationTheory.QuotSMulTop

/-!
# The torsion of a representation, and the connecting map of multiplication by a scalar

For a representation `ρ` of a monoid `G` on a module `V` over a commutative ring `k` and an
element `r : k`, every operator `ρ g` is `k`-linear and so preserves the `r`-torsion
`V[r] = Submodule.torsionBy k V r`. The representation therefore restricts to it; this is
`Representation.torsionBy`, the kernel counterpart of the reduction `Representation.quotSMulTop`
on the cokernel `V ⧸ rV`. An intertwining map restricts to the torsion
(`Representation.IntertwiningMap.torsionBy`), as it reduces modulo `r`
(`Representation.IntertwiningMap.quotSMulTop`).

For a short exact sequence `0 → V₁ → V₂ → V₃ → 0` of representations, the snake lemma for
multiplication by `r` gives the six-term exact sequence

`0 → V₁[r] → V₂[r] → V₃[r] → V₁ ⧸ rV₁ → V₂ ⧸ rV₂ → V₃ ⧸ rV₃ → 0`

of `TauCeti/Algebra/Module/Torsion/Snake.lean`. Each `g : G` acts on the short exact sequence by
a morphism of short exact sequences, so naturality of the connecting map
(`TauCeti.torsionByδ_comp_torsionByMap`) makes it intertwining
(`Representation.IntertwiningMap.torsionByδ`): the whole six-term sequence is a sequence of
representations. For `k = ℤ`, `r = ℓ` a prime and `G` a group acting on abelian groups, this is
the sequence of `G`-modules behind the comparison of `V ⧸ ℓV` with `V[ℓ]` in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, (7.3.3).

## Main definitions

* `Representation.torsionBy`: the representation induced by `ρ` on the `r`-torsion `V[r]`.
* `Representation.IntertwiningMap.torsionBy`: the restriction of an intertwining map to the
  `r`-torsion.
* `Representation.IntertwiningMap.torsionByδ`: the connecting map `V₃[r] → V₁ ⧸ rV₁` of a short
  exact sequence of representations, as an intertwining map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, (7.3.3).
-/

public section

open Function

namespace Representation

variable {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V]

/-- The representation induced by `ρ` on the `r`-torsion `V[r] = Submodule.torsionBy k V r`:
Mathlib's subrepresentation on the `G`-stable submodule `V[r]`. Its operators are the
restrictions `TauCeti.torsionByMap r (ρ g)` (`Representation.torsionBy_apply`). -/
noncomputable def torsionBy (ρ : Representation k G V) (r : k) :
    Representation k G (Submodule.torsionBy k V r) :=
  ρ.subrepresentation (Submodule.torsionBy k V r) fun g x hx ↦ by
    rw [Submodule.mem_comap, Submodule.mem_torsionBy_iff] at *
    rw [← map_smul, hx, map_zero]

/-- The operators of `ρ.torsionBy r` are the restrictions `TauCeti.torsionByMap r (ρ g)`. -/
@[simp]
theorem torsionBy_apply (ρ : Representation k G V) (r : k) (g : G) :
    ρ.torsionBy r g = TauCeti.torsionByMap r (ρ g) := by
  ext x
  rw [TauCeti.coe_torsionByMap_apply]
  rfl

/-- `ρ.torsionBy r g` acts on an `r`-torsion vector as `ρ g`. -/
theorem coe_torsionBy_apply (ρ : Representation k G V) (r : k) (g : G)
    (x : Submodule.torsionBy k V r) : (ρ.torsionBy r g x : V) = ρ g x :=
  (rfl)

namespace IntertwiningMap

variable {W : Type*} [AddCommGroup W] [Module k W] {ρ : Representation k G V}
  {σ : Representation k G W}

/-- **Restriction of an intertwining map to the `r`-torsion**: `TauCeti.torsionByMap r f`
intertwines `ρ.torsionBy r` and `σ.torsionBy r`. -/
noncomputable def torsionBy (f : IntertwiningMap ρ σ) (r : k) :
    IntertwiningMap (ρ.torsionBy r) (σ.torsionBy r) where
  toLinearMap := TauCeti.torsionByMap r f.toLinearMap
  isIntertwining' g := by
    rw [torsionBy_apply, torsionBy_apply, ← TauCeti.torsionByMap_comp,
      ← TauCeti.torsionByMap_comp, f.isIntertwining']

/-- The linear map underlying the restriction of an intertwining map is `TauCeti.torsionByMap`. -/
@[simp]
theorem toLinearMap_torsionBy (f : IntertwiningMap ρ σ) (r : k) :
    (f.torsionBy r).toLinearMap = TauCeti.torsionByMap r f.toLinearMap :=
  (rfl)

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module k V₁] [AddCommGroup V₂] [Module k V₂]
  [AddCommGroup V₃] [Module k V₃] {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
  {ρ₃ : Representation k G V₃} {f : IntertwiningMap ρ₁ ρ₂} {g : IntertwiningMap ρ₂ ρ₃}

/-- **The connecting map of a short exact sequence of representations** for multiplication by
`r`: the snake-lemma map `TauCeti.torsionByδ r : V₃[r] → V₁ ⧸ rV₁` of
`0 → V₁ → V₂ → V₃ → 0` intertwines `ρ₃.torsionBy r` and `ρ₁.quotSMulTop r`. Each `γ : G` acts on
the sequence by the morphism `(ρ₁ γ, ρ₂ γ, ρ₃ γ)`, which the connecting map commutes with by
naturality. -/
noncomputable def torsionByδ (r : k) (hfg : Exact f g) (hf : Injective f) (hg : Surjective g) :
    IntertwiningMap (ρ₃.torsionBy r) (ρ₁.quotSMulTop r) where
  toLinearMap := TauCeti.torsionByδ r (f := f.toLinearMap) (g := g.toLinearMap) hfg hf hg
  isIntertwining' γ := by
    rw [torsionBy_apply, quotSMulTop_apply]
    exact TauCeti.torsionByδ_comp_torsionByMap hfg hf hg hfg hf hg (f.isIntertwining' γ).symm
      (g.isIntertwining' γ).symm

/-- The linear map underlying the connecting map of representations is `TauCeti.torsionByδ`. -/
@[simp]
theorem toLinearMap_torsionByδ (r : k) (hfg : Exact f g) (hf : Injective f)
    (hg : Surjective g) :
    (torsionByδ r hfg hf hg).toLinearMap =
      TauCeti.torsionByδ r (f := f.toLinearMap) (g := g.toLinearMap) hfg hf hg :=
  (rfl)

end IntertwiningMap

end Representation
