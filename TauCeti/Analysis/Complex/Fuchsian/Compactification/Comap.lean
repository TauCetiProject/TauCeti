/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Conj
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

If `Γ' = g Γ g⁻¹`, translation by `g` induces a biholomorphism of compactified quotients
(`Subgroup.CompactifiedQuotient.conjBiholomorph`), and pulling back along it is an isomorphism of
function fields `M(X_Γ') ≃ M(X_Γ)`. For `g` in the normalizer of `Γ` this is an automorphism of
`M(X_Γ)`, `F ↦ F ∘ g`. These automorphisms form a right action of the normalizer, trivial on `Γ`
itself, and they fix the pullbacks of functions from the compactified quotient of any larger group
containing `g`. For `Γ(N) ⊴ SL(2, ℤ)` this is the action of `SL(2, ℤ/Nℤ) / {±1}` on the function
field of `X(N)` by fractional linear maps, which fixes the functions pulled back from `X(1)`.

## Main declarations

* `Subgroup.exists_compactifiedQuotientMap_ne`: the map of compactified quotients is not
  constant.
* `Subgroup.compactifiedQuotientComap`: the pullback of meromorphic functions, as a homomorphism of
  `ℂ`-algebras.
* `Subgroup.compactifiedQuotientComap_injective`: the pullback is a field embedding.
* `Subgroup.compactifiedQuotientComap_refl` and `Subgroup.compactifiedQuotientComap_trans`: it is
  functorial in the subgroup inclusion.
* `Subgroup.compactifiedQuotientConjComap`: the pullback along the biholomorphism induced by a
  conjugation, as an isomorphism of `ℂ`-algebras, with its composition law
  `Subgroup.compactifiedQuotientConjComap_trans` and its compatibility
  `Subgroup.compactifiedQuotientConjComap_compactifiedQuotientComap` with the pullbacks along
  inclusions.
* `Subgroup.compactifiedQuotientNormalizerComap`: the right action of the normalizer of `Γ` on the
  function field, trivial on `Γ` (`Subgroup.compactifiedQuotientNormalizerComap_eq_one`) and fixing
  pullbacks from larger groups
  (`Subgroup.unop_compactifiedQuotientNormalizerComap_compactifiedQuotientComap`).

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §7.5 (the function fields of modular curves and the maps
  between them).
* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §6.1 (the action of `SL(2, ℤ)` on the modular functions of level `N`).
-/

public noncomputable section

open MulAction MulOpposite TauCeti.RiemannSurface
open scoped MatrixGroups Pointwise UpperHalfPlane

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

/-! ### Pulling back along conjugations -/

section Conj

variable {Γ' Δ' : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ'] {g g' : PSL(2, ℝ)}

/-- **The pullback along a conjugation.** If `Γ' = g Γ g⁻¹`, pulling back along the
biholomorphism of compactified quotients induced by `g`
(`Subgroup.CompactifiedQuotient.conjBiholomorph`) is an isomorphism of function fields
`M(X_Γ') ≃ₐ[ℂ] M(X_Γ)`. It sends `F` to the function whose value at the orbit of `z` is the
value of `F` at the orbit of `g • z`. -/
def compactifiedQuotientConjComap (h : ConjAct.toConjAct g • Γ = Γ') :
    MeromorphicFunction Γ'.CompactifiedQuotient ≃ₐ[ℂ] MeromorphicFunction Γ.CompactifiedQuotient :=
  MeromorphicFunction.comapAlgEquiv (CompactifiedQuotient.conjBiholomorph h)

/-- The pullback of `F` along a conjugation takes the value of `F` at the image point. -/
@[simp]
theorem compactifiedQuotientConjComap_apply (h : ConjAct.toConjAct g • Γ = Γ')
    (F : MeromorphicFunction Γ'.CompactifiedQuotient) (x : Γ.CompactifiedQuotient) :
    compactifiedQuotientConjComap h F x = F (compactifiedQuotientConj h x) := by
  rw [compactifiedQuotientConjComap, MeromorphicFunction.comapAlgEquiv_apply,
    CompactifiedQuotient.coe_conjBiholomorph]

/-- The finite part of the pullback of `F` along a conjugation is the finite part of `F` at the
image point. -/
@[simp]
theorem finitePart_compactifiedQuotientConjComap (h : ConjAct.toConjAct g • Γ = Γ')
    (F : MeromorphicFunction Γ'.CompactifiedQuotient) :
    (compactifiedQuotientConjComap h F).finitePart = F.finitePart ∘ compactifiedQuotientConj h := by
  rw [compactifiedQuotientConjComap, MeromorphicFunction.finitePart_comapAlgEquiv,
    CompactifiedQuotient.coe_conjBiholomorph]

/-- The inverse of the pullback along the conjugation by `g` is the pullback along the
conjugation by `g⁻¹`. -/
@[simp]
theorem compactifiedQuotientConjComap_symm (h : ConjAct.toConjAct g • Γ = Γ') :
    (compactifiedQuotientConjComap h).symm =
      compactifiedQuotientConjComap (by rw [← h, map_inv, inv_smul_smul] :
        ConjAct.toConjAct g⁻¹ • Γ' = Γ) := by
  rw [compactifiedQuotientConjComap, MeromorphicFunction.comapAlgEquiv_symm,
    CompactifiedQuotient.conjBiholomorph_symm, compactifiedQuotientConjComap]

/-- Pulling back along the conjugation by an element of `Γ` does nothing. -/
@[simp]
theorem compactifiedQuotientConjComap_of_mem (hg : g ∈ Γ) (h : ConjAct.toConjAct g • Γ = Γ) :
    compactifiedQuotientConjComap h = AlgEquiv.refl :=
  AlgEquiv.ext fun F ↦ MeromorphicFunction.ext fun x ↦ by
    rw [compactifiedQuotientConjComap_apply, compactifiedQuotientConj_of_mem hg, id,
      AlgEquiv.coe_refl, id]

/-- **Functoriality of the pullback along conjugations.** Pulling back along the conjugation by
`g' * g` is pulling back along the conjugation by `g'` and then along the conjugation by `g`. -/
theorem compactifiedQuotientConjComap_trans {Γ'' : Subgroup PSL(2, ℝ)} [DiscreteTopology Γ'']
    (h : ConjAct.toConjAct g • Γ = Γ') (h' : ConjAct.toConjAct g' • Γ' = Γ'') :
    compactifiedQuotientConjComap (by rw [map_mul, mul_smul, h, h'] :
        ConjAct.toConjAct (g' * g) • Γ = Γ'') =
      (compactifiedQuotientConjComap h').trans (compactifiedQuotientConjComap h) :=
  AlgEquiv.ext fun F ↦ MeromorphicFunction.ext fun x ↦ by
    rw [AlgEquiv.trans_apply, compactifiedQuotientConjComap_apply,
      compactifiedQuotientConjComap_apply, compactifiedQuotientConjComap_apply,
      ← compactifiedQuotientConj_comp h h', Function.comp_apply]

/-- **Pulling back along conjugations commutes with the level maps.** If `g` conjugates `Δ ≤ Γ` to
`Δ' ≤ Γ'`, then pulling back from `Γ'` to `Δ'` and then along the conjugation of `Δ` agrees with
pulling back along the conjugation of `Γ` and then from `Γ` to `Δ`. -/
theorem compactifiedQuotientConjComap_compactifiedQuotientComap [DiscreteTopology Δ']
    (hΔ : ConjAct.toConjAct g • Δ = Δ') (hΓ : ConjAct.toConjAct g • Γ = Γ') (hle : Δ ≤ Γ)
    (hle' : Δ' ≤ Γ') (F : MeromorphicFunction Γ'.CompactifiedQuotient) :
    compactifiedQuotientConjComap hΔ (compactifiedQuotientComap hle' F) =
      compactifiedQuotientComap hle (compactifiedQuotientConjComap hΓ F) :=
  MeromorphicFunction.ext fun x ↦ by
    simp [compactifiedQuotientMap_compactifiedQuotientConj hΔ hΓ hle hle']

end Conj

/-! ### The action of the normalizer -/

section Normalizer

variable (Γ) in
/-- **The normalizer acts on the function field.** An element `g` of the normalizer of a discrete
`Γ` acts on the meromorphic functions on the compactified quotient of `Γ` by pulling back along
the biholomorphism induced by `g`, sending `F` to the function `Γ z ↦ F (Γ (g • z))`. This is a
right action, `F ↦ F ∘ g`: acting by `g * g'` is acting by `g` and then by `g'`. So it is a
homomorphism to the opposite of the automorphism group of the function field. -/
def compactifiedQuotientNormalizerComap :
    normalizer (Γ : Set PSL(2, ℝ)) →*
      (MeromorphicFunction Γ.CompactifiedQuotient ≃ₐ[ℂ]
        MeromorphicFunction Γ.CompactifiedQuotient)ᵐᵒᵖ where
  toFun g := op (compactifiedQuotientConjComap (conjAct_pointwise_smul_iff.mpr g.2))
  map_one' := congrArg op (compactifiedQuotientConjComap_of_mem Γ.one_mem _)
  map_mul' g g' := by
    rw [← op_mul, AlgEquiv.aut_mul]
    exact congrArg op (compactifiedQuotientConjComap_trans _ _)

/-- The action of an element `g` of the normalizer sends `F` to its pullback along the conjugation
by `g`. -/
theorem unop_compactifiedQuotientNormalizerComap (g : normalizer (Γ : Set PSL(2, ℝ)))
    (h : ConjAct.toConjAct (g : PSL(2, ℝ)) • Γ = Γ) :
    unop (compactifiedQuotientNormalizerComap Γ g) = compactifiedQuotientConjComap h :=
  (rfl)

/-- Elements of `Γ` act trivially on the function field of the compactified quotient of `Γ`. -/
theorem compactifiedQuotientNormalizerComap_eq_one {g : normalizer (Γ : Set PSL(2, ℝ))}
    (hg : (g : PSL(2, ℝ)) ∈ Γ) : compactifiedQuotientNormalizerComap Γ g = 1 :=
  congrArg op (compactifiedQuotientConjComap_of_mem hg _)

/-- **Pullbacks from a larger group are invariant.** If `Δ ≤ Γ` and `g ∈ Γ` normalizes `Δ`, then
the pullback to the compactified quotient of `Δ` of a meromorphic function on that of `Γ` is fixed
by `g`. -/
theorem unop_compactifiedQuotientNormalizerComap_compactifiedQuotientComap (h : Δ ≤ Γ)
    {g : normalizer (Δ : Set PSL(2, ℝ))} (hg : (g : PSL(2, ℝ)) ∈ Γ)
    (F : MeromorphicFunction Γ.CompactifiedQuotient) :
    unop (compactifiedQuotientNormalizerComap Δ g) (compactifiedQuotientComap h F) =
      compactifiedQuotientComap h F := by
  have hΓ : ConjAct.toConjAct (g : PSL(2, ℝ)) • Γ = Γ :=
    conjAct_pointwise_smul_eq_self (le_normalizer hg)
  rw [unop_compactifiedQuotientNormalizerComap g (conjAct_pointwise_smul_iff.mpr g.2),
    compactifiedQuotientConjComap_compactifiedQuotientComap _ hΓ h h,
    compactifiedQuotientConjComap_of_mem hg, AlgEquiv.coe_refl, id]

end Normalizer

end Subgroup
