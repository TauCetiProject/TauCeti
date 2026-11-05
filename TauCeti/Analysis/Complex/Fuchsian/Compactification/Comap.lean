/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Holomorphic
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Comap
import TauCeti.Analysis.Complex.Fuchsian.Covolume

/-!
# Pulling meromorphic functions back along maps of compactified quotients

An inclusion `Δ ≤ Γ` of discrete subgroups of `PSL(2, ℝ)` induces a holomorphic map
`Subgroup.compactifiedQuotientMap` of their compactified quotients. It is never constant: a
discrete subgroup is countable, so its orbits in the uncountable upper half-plane are countable,
and points in different orbits have different images. Pulling back along it therefore embeds the
field of meromorphic functions on the compactified quotient of `Γ` into that of `Δ`. For
congruence subgroups these are the level maps between fields of modular functions, for example
the inclusion of the field of the level-one curve `X(1)` into that of `X(N)`.

## Main declarations

* `Subgroup.exists_compactifiedQuotientMap_ne`: the map of compactified quotients is not
  constant.
* `Subgroup.compactifiedQuotientComap`: the pullback of meromorphic functions, as a homomorphism of
  `ℂ`-algebras.
* `Subgroup.compactifiedQuotientComap_injective`: the pullback is a field embedding.
* `Subgroup.compactifiedQuotientComap_refl` and `Subgroup.compactifiedQuotientComap_trans`: it is
  functorial in the subgroup inclusion.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §7.5 (the function fields of modular curves and the maps
  between them).
-/

public noncomputable section

open MulAction TauCeti.RiemannSurface
open scoped MatrixGroups UpperHalfPlane

namespace Subgroup

variable {Δ Γ Θ : Subgroup PSL(2, ℝ)}

/-- **The map of compactified quotients is not constant.** For an inclusion `Δ ≤ Γ` with `Γ`
discrete, the orbit of `I` under the countable group `Γ` is countable, so it misses a point of the
uncountable upper half-plane, and the orbits of these two points have different images. -/
theorem exists_compactifiedQuotientMap_ne [DiscreteTopology Γ] (h : Δ ≤ Γ) :
    ∃ x₁ x₂ : Δ.CompactifiedQuotient,
      compactifiedQuotientMap h x₁ ≠ compactifiedQuotientMap h x₂ := by
  obtain ⟨z, hz⟩ : ∃ z : ℍ, z ∉ orbit Γ UpperHalfPlane.I := by
    by_contra! hall
    have hcount : (Set.univ : Set ℍ).Countable :=
      (Set.countable_range fun g : Γ ↦ g • UpperHalfPlane.I).mono fun z _ ↦ hall z
    -- the horizontal line `t ↦ t + I` embeds the uncountable `ℝ` into the upper half-plane
    have hinj : Function.Injective fun t : ℝ ↦ (⟨t + Complex.I, by simp⟩ : ℍ) := fun s t hst ↦ by
      simpa using congrArg (fun z : ℍ ↦ (z : ℂ).re) hst
    have : Countable ℍ := Set.countable_univ_iff.mp hcount
    exact not_countable (α := ℝ) hinj.countable
  refine ⟨.ofQuotient (Quotient.mk _ UpperHalfPlane.I), .ofQuotient (Quotient.mk _ z),
    fun he ↦ hz ?_⟩
  rw [compactifiedQuotientMap_ofQuotient, compactifiedQuotientMap_ofQuotient] at he
  have he' := CompactifiedQuotient.ofQuotient_injective he
  rw [TauCeti.Setoid.map_of_le_mk, TauCeti.Setoid.map_of_le_mk] at he'
  exact orbitRel_apply.mp (Quotient.exact he'.symm)

/-- **The pullback of meromorphic functions** along the map of compactified quotients induced by
an inclusion `Δ ≤ Γ` of discrete subgroups of `PSL(2, ℝ)`, as a homomorphism of `ℂ`-algebras
`F ↦ F ∘ compactifiedQuotientMap h`. -/
def compactifiedQuotientComap [DiscreteTopology Δ] [DiscreteTopology Γ] (h : Δ ≤ Γ) :
    MeromorphicFunction Γ.CompactifiedQuotient →ₐ[ℂ] MeromorphicFunction Δ.CompactifiedQuotient :=
  MeromorphicFunction.comapₐ (compactifiedQuotientMap h)
    (CompactifiedQuotient.mdifferentiable_compactifiedQuotientMap h)
    (exists_compactifiedQuotientMap_ne h)

variable [DiscreteTopology Δ] [DiscreteTopology Γ] (h : Δ ≤ Γ)

/-- The pullback of `F` takes the value of `F` at the image point. -/
@[simp]
theorem compactifiedQuotientComap_apply (F : MeromorphicFunction Γ.CompactifiedQuotient)
    (x : Δ.CompactifiedQuotient) :
    compactifiedQuotientComap h F x = F (compactifiedQuotientMap h x) := by
  rw [compactifiedQuotientComap, MeromorphicFunction.comapₐ_apply,
    MeromorphicFunction.comap_apply]

/-- The finite part of the pullback of `F` is the finite part of `F` at the image point. -/
@[simp]
theorem finitePart_compactifiedQuotientComap (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    (compactifiedQuotientComap h F).finitePart = F.finitePart ∘ compactifiedQuotientMap h := by
  rw [compactifiedQuotientComap, MeromorphicFunction.comapₐ_apply,
    MeromorphicFunction.finitePart_comap]

/-- **The pullback is a field embedding.** -/
theorem compactifiedQuotientComap_injective : Function.Injective (compactifiedQuotientComap h) :=
  MeromorphicFunction.comapₐ_injective _ _ _

/-- Pulling back along the identity inclusion does nothing. -/
@[simp]
theorem compactifiedQuotientComap_refl (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    compactifiedQuotientComap (le_refl Γ) F = F :=
  MeromorphicFunction.ext fun x ↦ by simp

/-- **Functoriality of the pullback.** Pulling back along `Δ ≤ Θ` is pulling back along `Γ ≤ Θ`
and then along `Δ ≤ Γ`. -/
theorem compactifiedQuotientComap_trans [DiscreteTopology Θ] (k : Γ ≤ Θ)
    (F : MeromorphicFunction Θ.CompactifiedQuotient) :
    compactifiedQuotientComap (h.trans k) F =
      compactifiedQuotientComap h (compactifiedQuotientComap k F) :=
  MeromorphicFunction.ext fun x ↦ by simp

end Subgroup
