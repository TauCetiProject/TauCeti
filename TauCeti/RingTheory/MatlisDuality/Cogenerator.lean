/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MatlisDuality.Basic

/-!
# A cogenerator over its endomorphism ring

Let `R` be a commutative ring, `E` an `R`-module, `A` an `R`-algebra and `D = Hom_R(-, E)` the
Matlis dual. Let `M` be a left `A`-module and `Γ = Module.End A M`, acting on `M` by evaluation.
Suppose that `D A`, the dual of the right regular module, is a direct summand of a finite sum of
copies of `M`, in the form of `A`-linear maps `aⱼ : D A → M` and `bⱼ : M → D A` with
`∑ⱼ bⱼ ∘ aⱼ = 1`. For an Artin algebra and an injective hull `E` of `R ⧸ J(R)`, this says that `M`
is a cogenerator of `mod A`.

Then the dual `D M` is a projective right `Γ`-module
(`TauCeti.MatlisDual.projective_of_sum_comp_eq_id`), and if `E` is injective, `M` has finite length
over `R` and each `Hom_R(R ⧸ 𝔪, E)` has length one, then `M` is an injective `Γ`-module
(`TauCeti.MatlisDual.injective_end_of_sum_comp_eq_id`): it is the dual of the projective right
module `D M`. These are the duals of the statements that a generator is projective over its
endomorphism ring (`TauCeti.Module.IsGenerator.projective_end`).

## Implementation notes

`D M` is a direct summand of `Γⁿ` as a right `Γ`-module. Its `j`-th coordinate sends `ψ` to
`aⱼ ∘ adj ψ`, where `adj ψ : M → D A`, `x ↦ (a ↦ ψ (a • x))`, is the map given by the
Hom-tensor adjunction `TauCeti.MatlisDual.equivLinearMapDualRegular`. The projection back onto
`D M` sends the `j`-th basis vector of `Γⁿ` to the functional `x ↦ bⱼ x 1` of `D M`, the image of
`bⱼ` under the inverse of the adjunction.

## Main results

* `TauCeti.MatlisDual.projective_of_sum_comp_eq_id`: `D M` is a projective right `Γ`-module.
* `TauCeti.MatlisDual.injective_end_of_sum_comp_eq_id`: `M` is an injective `Γ`-module.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Proposition VI.5.4(a).
-/

public section

noncomputable section

namespace TauCeti

open MulOpposite

universe u v w t

namespace MatlisDual

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {A : Type t} [Ring A] [Algebra R A]
  {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The Hom-tensor adjunction `D M ≅ Hom_A(M, D A)` turns the right action of `Γ` on `D M` into
precomposition. -/
private theorem equivLinearMapDualRegular_smul (g : (Module.End A M)ᵐᵒᵖ)
    (ψ : MatlisDual R E M) :
    equivLinearMapDualRegular (A := A) (g • ψ) = equivLinearMapDualRegular ψ ∘ₗ g.unop := by
  ext x a
  simp [Module.End.smul_def]

/-- The coordinate `ψ ↦ c ∘ adj ψ` of `D M` in `Γ`, a map of right `Γ`-modules. -/
private def coord (c : MatlisDual R E A →ₗ[A] M) :
    MatlisDual R E M →ₗ[(Module.End A M)ᵐᵒᵖ] (Module.End A M)ᵐᵒᵖ where
  toFun ψ := op (c ∘ₗ equivLinearMapDualRegular ψ)
  map_add' ψ φ := by simp [LinearMap.comp_add]
  map_smul' g ψ := by
    simp only [equivLinearMapDualRegular_smul, RingHom.id_apply, smul_eq_mul]
    rfl

variable {ι : Type*} [Fintype ι]

/-- **The dual of a cogenerator is projective over its endomorphism ring.** If `D A` is a direct
summand of a finite sum of copies of `M`, through `aⱼ : D A → M` and `bⱼ : M → D A` with
`∑ⱼ bⱼ ∘ aⱼ = 1`, then `D M` is a projective right module over `Γ = Module.End A M`, as a direct
summand of `Γⁿ`. -/
theorem projective_of_sum_comp_eq_id (a : ι → MatlisDual R E A →ₗ[A] M)
    (b : ι → M →ₗ[A] MatlisDual R E A) (h : ∑ j, b j ∘ₗ a j = LinearMap.id) :
    Module.Projective (Module.End A M)ᵐᵒᵖ (MatlisDual R E M) := by
  classical
  refine .of_split (LinearMap.pi fun j ↦ coord (a j))
    ((LinearEquiv.piRing _ _ ι ℕ).symm fun j ↦ equivLinearMapDualRegular.symm (b j))
    (LinearMap.ext fun ψ ↦ MatlisDual.ext fun x ↦ ?_)
  have hx := congr(equivLinearMap R E A ($h (equivLinearMapDualRegular ψ x)) 1)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum, LinearMap.id_apply,
    equivLinearMapDualRegular_apply_apply, one_smul] at hx
  simpa [coord, Module.End.smul_def] using hx

/-- **A cogenerator is injective over its endomorphism ring.** Let `E` be injective with each
`Hom_R(R ⧸ 𝔪, E)` of length one, and `M` of finite length over `R`. If `D A` is a direct summand of
a finite sum of copies of `M`, through `aⱼ : D A → M` and `bⱼ : M → D A` with `∑ⱼ bⱼ ∘ aⱼ = 1`, then
`M` is an injective module over `Γ = Module.End A M`: by biduality it is the dual of the projective
right `Γ`-module `D M` (`TauCeti.MatlisDual.projective_of_sum_comp_eq_id`). -/
theorem injective_end_of_sum_comp_eq_id [Module.Injective R E] [Small.{v} R]
    (hE : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → Module.length R (R ⧸ 𝔪 →ₗ[R] E) = 1)
    (hM : IsFiniteLength R M) (a : ι → MatlisDual R E A →ₗ[A] M)
    (b : ι → M →ₗ[A] MatlisDual R E A) (h : ∑ j, b j ∘ₗ a j = LinearMap.id) :
    Module.Injective (Module.End A M) M :=
  have := projective_of_sum_comp_eq_id a b h
  ((Module.Baer.of_injective inferInstance).of_equiv
    (evalEquiv (A := Module.End A M) hE hM).symm).injective

end MatlisDual

end TauCeti
