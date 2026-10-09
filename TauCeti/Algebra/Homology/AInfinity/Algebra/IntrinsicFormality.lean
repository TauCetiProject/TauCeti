/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Formal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Comap
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Cohomology

/-!
# Intrinsically formal graded algebras

A graded algebra `H` is **intrinsically formal** when every `A∞` algebra whose cohomology algebra
is isomorphic to `H` is formal: the cohomology algebra alone then determines every such `A∞`
algebra up to quasi-isomorphism.
Here `H` is presented as an `A∞` algebra `ℋ`, normally minimal with no operations above arity two,
and an isomorphism of cohomology algebras is a bijective strict morphism from `ℋ` to the
cohomology `A∞` algebra `TauCeti.AInfinityAlgebra.cohomologyAInfinityAlgebra`.

Minimality, formality and intrinsic formality are distinct predicates.  Minimality (`m₁ = 0`) is
a property of one `A∞` structure; formality asks for a quasi-isomorphism from one `A∞` algebra to
its cohomology algebra; intrinsic formality is a property of a graded algebra, quantifying over
all `A∞` algebras with that cohomology.

The definition quantifies over all `A∞` algebras, while intrinsic formality is established by
studying `A∞` structures on `H` itself, as in Kadeishvili's obstruction theory.  Over a field the
two agree: `ℋ` is intrinsically formal exactly when every minimal `A∞` structure on `H` with the
grading and the binary operation of `ℋ` is formal (`isIntrinsicallyFormal_iff`), equivalently
`A∞` isomorphic to `ℋ` (`isIntrinsicallyFormal_iff_forall_exists_isIso`).  The reduction is
Kadeishvili's theorem: an `A∞` algebra is quasi-isomorphic to its minimal model on cohomology,
and the isomorphism of cohomology algebras pulls that model back to a minimal structure on `H`.

For example, an `A∞` algebra concentrated in degree zero has no operation besides `m₂`, so over a
field a graded algebra concentrated in degree zero is intrinsically formal
(`isIntrinsicallyFormal_of_forall_mem_piece_zero`): every `A∞` algebra whose cohomology is an
ordinary associative algebra in degree zero is formal.

## Main definitions

* `TauCeti.AInfinityAlgebra.IsIntrinsicallyFormal`: every `A∞` algebra whose cohomology algebra
  is isomorphic to the given graded algebra is formal.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.isFormal_iff_exists_isIso`: a minimal `A∞` structure with
  the grading and binary operation of a graded algebra is formal exactly when it is `A∞` isomorphic
  to that graded algebra.
* `TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_isFormal`,
  `TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_iff` and
  `TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_iff_forall_exists_isIso`: over a field,
  intrinsic formality is a statement about minimal `A∞` structures on the graded algebra itself.
* `TauCeti.AInfinityAlgebra.isIntrinsicallyFormal_of_forall_mem_piece_zero`: over a field, a
  graded algebra concentrated in degree zero is intrinsically formal.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
-/

public section

namespace TauCeti

universe uR uK uH

namespace AInfinityAlgebra

section CommRing

variable {R : Type uR} {H : Type uH} [CommRing R] [AddCommGroup H] [Module R H]

/-- A graded algebra, presented as an `A∞` algebra `ℋ`, is **intrinsically formal** when every
`A∞` algebra whose cohomology algebra is isomorphic to `ℋ`, through a bijective strict morphism
from `ℋ` to its cohomology `A∞` algebra, is formal.  The `A∞` algebras quantified over have
carriers in the universe of `H`. -/
def IsIntrinsicallyFormal (ℋ : AInfinityAlgebra R H) : Prop :=
  ∀ ⦃A : Type uH⦄ [AddCommGroup A] [Module R A] (𝒜 : AInfinityAlgebra R A)
    (f : AInfinityStrictHom ℋ 𝒜.cohomologyAInfinityAlgebra), Function.Bijective f → 𝒜.IsFormal

/-- Unfold intrinsic formality: every `A∞` algebra with a cohomology algebra isomorphic to `ℋ` is
formal. -/
theorem isIntrinsicallyFormal_def (ℋ : AInfinityAlgebra R H) :
    ℋ.IsIntrinsicallyFormal ↔ ∀ ⦃A : Type uH⦄ [AddCommGroup A] [Module R A]
      (𝒜 : AInfinityAlgebra R A) (f : AInfinityStrictHom ℋ 𝒜.cohomologyAInfinityAlgebra),
      Function.Bijective f → 𝒜.IsFormal := Iff.rfl

variable {ℋ ℬ : AInfinityAlgebra R H}

/-- An `A∞` algebra whose cohomology algebra is isomorphic to an intrinsically formal graded
algebra is formal. -/
theorem IsIntrinsicallyFormal.isFormal (h : ℋ.IsIntrinsicallyFormal) {A : Type uH}
    [AddCommGroup A] [Module R A] (𝒜 : AInfinityAlgebra R A)
    (f : AInfinityStrictHom ℋ 𝒜.cohomologyAInfinityAlgebra) (hf : Function.Bijective f) :
    𝒜.IsFormal :=
  h 𝒜 f hf

/-- A minimal `A∞` structure `ℬ` with the grading and the binary operation of a minimal `ℋ`
without operations above arity two is formal exactly when it is `A∞` isomorphic to `ℋ`. -/
theorem IsMinimal.isFormal_iff_exists_isIso (hℬ : ℬ.IsMinimal) (hℋ : ℋ.IsMinimal)
    (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) (hG : ℬ.grading = ℋ.grading) (h₂ : ℬ.m 2 = ℋ.m 2) :
    ℬ.IsFormal ↔ ∃ f : AInfinityHom ℬ ℋ, f.IsIso := by
  refine ⟨fun hℬf ↦ ?_, fun ⟨f, hf⟩ ↦ (hℋ.isFormal hm).of_isQuasiIso hf.isQuasiIso⟩
  obtain ⟨g, hg⟩ := (isFormal_def ℬ).1 hℬf
  -- Follow `g : ℬ ⟶ H(ℬ)` by the inverse of the identification `ℋ ≅ H(ℬ)`.
  let s := (hℬ.toCohomology hℋ hm hG h₂).toAInfinityHom
  have hs : Function.Bijective s.linearPart := by
    rw [AInfinityStrictHom.linearPart_toAInfinityHom, AInfinityStrictHom.coe_toLinearMap]
    exact hℬ.bijective_toCohomology hℋ hm hG h₂
  exact ⟨(s.inverse hs).comp g, (AInfinityHom.isIso_inverse s hs).comp
    (hg.isIso hℬ ℬ.isMinimal_cohomologyAInfinityAlgebra)⟩

/-- Every minimal `A∞` structure with the grading and the binary operation of an intrinsically
formal graded algebra is formal. -/
theorem IsIntrinsicallyFormal.isFormal_of_isMinimal (h : ℋ.IsIntrinsicallyFormal)
    (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) (hG : ℬ.grading = ℋ.grading)
    (hℬ : ℬ.IsMinimal) (h₂ : ℬ.m 2 = ℋ.m 2) : ℬ.IsFormal :=
  h ℬ (hℬ.toCohomology hℋ hm hG h₂) (hℬ.bijective_toCohomology hℋ hm hG h₂)

end CommRing

section Field

variable {K : Type uK} {H : Type uH} [Field K] [AddCommGroup H] [Module K H]
  {ℋ : AInfinityAlgebra K H}

/-- Over a field, a graded algebra `ℋ` is intrinsically formal as soon as every minimal `A∞`
structure on the same graded module with the same binary operation is formal. -/
theorem isIntrinsicallyFormal_of_forall_isFormal (h : ∀ ℬ : AInfinityAlgebra K H,
    ℬ.grading = ℋ.grading → ℬ.IsMinimal → ℬ.m 2 = ℋ.m 2 → ℬ.IsFormal) :
    ℋ.IsIntrinsicallyFormal := by
  intro A _ _ 𝒜 f hf
  -- Pull the minimal model of `𝒜` back to `H` along the isomorphism `f` of cohomology algebras.
  have hdeg (p : ℤ) (x : H) :
      f.toLinearMap x ∈ 𝒜.minimalModel.grading.piece p ↔ x ∈ ℋ.grading.piece p := by
    rw [minimalModel_grading, ← cohomologyAInfinityAlgebra_grading]
    exact f.map_mem_iff_of_bijective hf
  have hrange (n : ℕ) (_ : 0 < n) (x : Fin n → H) :
      𝒜.minimalModel.m n (fun i ↦ f.toLinearMap (x i)) ∈ LinearMap.range f.toLinearMap := by
    rw [LinearMap.range_eq_top.2 hf.2]
    exact Submodule.mem_top
  let ℬ := 𝒜.minimalModel.comap ℋ.grading f.toLinearMap hf.1 hdeg hrange
  have hfm (n : ℕ) (x : Fin n → H) : f (ℬ.m n x) = 𝒜.minimalModel.m n fun i ↦ f (x i) :=
    map_m_comap _ _ _ hf.1 hdeg hrange n x
  have hℬ : ℬ.IsMinimal := (isMinimal_iff_m_one_eq_zero ℬ).2 fun x ↦ hf.1 <| by
    rw [hfm, 𝒜.isMinimal_minimalModel.m_one, map_zero]
  have h₂ : ℬ.m 2 = ℋ.m 2 := MultilinearMap.ext fun x ↦ hf.1 <| by
    rw [hfm, f.map_m, cohomologyAInfinityAlgebra_m_two_apply,
      show (fun i ↦ f (x i)) = ![f (x 0), f (x 1)] from funext fun i ↦ by fin_cases i <;> rfl,
      minimalModel_m_two]
  -- The pullback is isomorphic to the minimal model, which is quasi-isomorphic to `𝒜`.
  let s := (𝒜.minimalModel.comapStrictHom ℋ.grading f.toLinearMap hf.1 hdeg hrange).toAInfinityHom
  have hs : Function.Bijective s.linearPart := by
    rw [AInfinityStrictHom.linearPart_toAInfinityHom, comapStrictHom_toLinearMap]
    exact hf
  exact ((h ℬ (comap_grading _ _ _ _ _ _) hℬ h₂).of_isQuasiIso
    (AInfinityHom.isIso_inverse s hs).isQuasiIso).of_isQuasiIso
    𝒜.isQuasiIso_minimalModelProjection

/-- Over a field, a minimal graded algebra `ℋ` without operations above arity two is
**intrinsically formal** exactly when every minimal `A∞` structure on the same graded module with
the same binary operation is formal. -/
theorem isIntrinsicallyFormal_iff (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) :
    ℋ.IsIntrinsicallyFormal ↔ ∀ ℬ : AInfinityAlgebra K H,
      ℬ.grading = ℋ.grading → ℬ.IsMinimal → ℬ.m 2 = ℋ.m 2 → ℬ.IsFormal :=
  ⟨fun h _ hG hℬ h₂ ↦ h.isFormal_of_isMinimal hℋ hm hG hℬ h₂,
    isIntrinsicallyFormal_of_forall_isFormal⟩

/-- Over a field, a minimal graded algebra `ℋ` without operations above arity two is
intrinsically formal exactly when every minimal `A∞` structure on the same graded module with the
same binary operation is `A∞` isomorphic to `ℋ`. -/
theorem isIntrinsicallyFormal_iff_forall_exists_isIso (hℋ : ℋ.IsMinimal)
    (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) :
    ℋ.IsIntrinsicallyFormal ↔ ∀ ℬ : AInfinityAlgebra K H,
      ℬ.grading = ℋ.grading → ℬ.IsMinimal → ℬ.m 2 = ℋ.m 2 → ∃ f : AInfinityHom ℬ ℋ, f.IsIso := by
  rw [isIntrinsicallyFormal_iff hℋ hm]
  exact forall_congr' fun ℬ ↦ forall_congr' fun hG ↦ forall_congr' fun hℬ ↦
    forall_congr' fun h₂ ↦ hℬ.isFormal_iff_exists_isIso hℋ hm hG h₂

/-- Over a field, a graded algebra concentrated in degree zero is intrinsically formal: every
`A∞` algebra whose cohomology algebra is isomorphic to it is formal. -/
theorem isIntrinsicallyFormal_of_forall_mem_piece_zero (h : ∀ x, x ∈ ℋ.grading.piece 0) :
    ℋ.IsIntrinsicallyFormal :=
  -- A structure with the grading of `ℋ` is concentrated in degree zero, so it has only `m₂`.
  isIntrinsicallyFormal_of_forall_isFormal fun ℬ hG hℬ _ ↦ hℬ.isFormal fun _ hn ↦
    ℬ.m_eq_zero_of_forall_mem_piece_zero (by rwa [hG]) (by omega)

end Field

end AInfinityAlgebra

end TauCeti
