/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal

/-!
# Formal `A∞` algebras

The cohomology `H(A)` of an `A∞` algebra `A` is a graded nonunital algebra, hence an `A∞`
algebra with zero `m₁`, the cohomology product as `m₂`, and no higher operations; this is
`AInfinityAlgebra.cohomologyAInfinityAlgebra`, and it is minimal.  The algebra `A` is *formal*
when it admits an `A∞` quasi-isomorphism to this `A∞` algebra.  Over a field every `A∞`
quasi-isomorphism has an `A∞` inverse up to homotopy, so there the direction of the
quasi-isomorphism is immaterial.
Minimal models are exactly what distinguishes the two notions: a minimal algebra is identified
with its cohomology as a graded algebra via `m₂`, while formality additionally asks that its higher
operations can be removed up to quasi-isomorphism.

Formality is reflected along quasi-isomorphisms: if `A ⟶ B` is a quasi-isomorphism and `B` is
formal, then so is `A`, because a quasi-isomorphism identifies the two cohomology algebras
compatibly with their gradings.  A minimal algebra whose operations above arity two vanish is
formal, since the class map is then a strict isomorphism onto its cohomology; in particular a
graded nonunital algebra with zero differential is formal.

## Main definitions

* `TauCeti.AInfinityAlgebra.IsFormal`: existence of an `A∞` quasi-isomorphism to
  `cohomologyAInfinityAlgebra`.
* `TauCeti.AInfinityAlgebra.IsMinimal.toCohomology`: the identification of a minimal algebra with
  its cohomology, as a strict morphism out of any minimal structure with the same grading and `m₂`
  and no higher operations.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.isFormal`: a minimal algebra with vanishing higher operations
  is formal. `TauCeti.IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_of_differential_eq_zero`
  applies this to DG algebras with zero differential.
* `TauCeti.AInfinityAlgebra.IsFormal.of_isQuasiIso`: formality is reflected along
  quasi-isomorphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
-/

public section

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

namespace AInfinityAlgebra

/-! ### Formality -/

/-- An `A∞` algebra is **formal** when it admits an `A∞` quasi-isomorphism to its cohomology,
regarded as an `A∞` algebra whose only nonzero operation is the cohomology product `m₂`. -/
def IsFormal (𝒜 : AInfinityAlgebra R A) : Prop :=
  ∃ f : AInfinityHom 𝒜 𝒜.cohomologyAInfinityAlgebra, f.IsQuasiIso

/-- An `A∞` algebra is formal exactly when it has a quasi-isomorphism to its cohomology `A∞`
algebra. -/
theorem isFormal_def (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsFormal ↔ ∃ f : AInfinityHom 𝒜 𝒜.cohomologyAInfinityAlgebra, f.IsQuasiIso := Iff.rfl

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- Formality is reflected along quasi-isomorphisms: if `𝒜 ⟶ ℬ` is a quasi-isomorphism and `ℬ` is
formal, then `𝒜` is formal. -/
theorem IsFormal.of_isQuasiIso {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) (hℬ : ℬ.IsFormal) :
    𝒜.IsFormal := by
  obtain ⟨g, hg⟩ := hℬ
  exact ⟨(hf.cohomologyStrictHomInv).toAInfinityHom.comp (g.comp f),
    hf.isQuasiIso_cohomologyStrictHomInv.comp (hg.comp hf)⟩

namespace IsMinimal

variable {ℋ : AInfinityAlgebra R A}

/-- For a minimal `𝒜`, and a minimal `A∞` structure `ℋ` on the same graded module with the same
binary operation and no operations above arity two, the identification of `A` with the cohomology
of `𝒜`, as a strict morphism from `ℋ` to the cohomology `A∞` algebra of `𝒜`.  Taking `ℋ = 𝒜`
identifies a minimal algebra with vanishing higher operations with its cohomology. -/
noncomputable def toCohomology (h : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal)
    (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) :
    AInfinityStrictHom ℋ 𝒜.cohomologyAInfinityAlgebra where
  toLinearMap := h.cohomologyEquiv.toLinearMap
  map_mem' hx := by
    rw [← hG] at hx
    simpa only [add_zero, cohomologyAInfinityAlgebra_grading] using
      h.isHomogeneous_cohomologyEquiv.map_mem hx
  map_m' n := by
    ext x
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
    match n with
    | 0 => simp
    | 1 => simp [hℋ.m_one]
    | 2 =>
      rw [cohomologyAInfinityAlgebra_m_two_apply, ← h₂]
      obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] :=
        ⟨x 0, x 1, funext fun i ↦ by fin_cases i <;> rfl⟩
      exact h.cohomologyEquiv_m_two a b
    | n + 3 => simp [hm (n + 3) (by omega)]

/-- The strict morphism `toCohomology` is the identification of a minimal algebra with its
cohomology. -/
@[simp]
theorem coe_toCohomology (h : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) :
    ⇑(h.toCohomology hℋ hm hG h₂) = h.cohomologyEquiv := (rfl)

/-- The strict morphism `toCohomology` is bijective. -/
theorem bijective_toCohomology (h : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal)
    (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) :
    Function.Bijective (h.toCohomology hℋ hm hG h₂) := by
  rw [coe_toCohomology]
  exact h.cohomologyEquiv.bijective

/-- A minimal `A∞` algebra whose operations of arity at least three vanish is formal: the
identification with its cohomology is a strict isomorphism. -/
theorem isFormal (h : 𝒜.IsMinimal) (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) : 𝒜.IsFormal := by
  refine ⟨(h.toCohomology h hm rfl rfl).toAInfinityHom, ?_⟩
  rw [AInfinityHom.isQuasiIso_iff_linearPart_bijective h 𝒜.isMinimal_cohomologyAInfinityAlgebra,
    AInfinityStrictHom.linearPart_toAInfinityHom]
  exact h.bijective_toCohomology h hm rfl rfl

end IsMinimal

end AInfinityAlgebra

/-- The `A∞` algebra of a nonunital DG algebra with vanishing differential is formal. -/
theorem IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_of_differential_eq_zero
    {A : Type uA} [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    {𝒜 : ℤ → Submodule R A} [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜]
    {d : A →ₗ[R] A} (h : IsNonUnitalDGAlgebra 𝒜 d) (hd : d = 0) :
    h.toAInfinityAlgebra.IsFormal :=
  ((h.isMinimal_toAInfinityAlgebra_iff).2 hd).isFormal fun _ hn ↦
    h.toAInfinityAlgebra_m_of_three_le hn

/-- The `A∞` algebra of a graded nonunital algebra with zero differential is formal. -/
theorem IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_zero {A : Type uA} [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (𝒜 : ℤ → Submodule R A)
    [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] :
    (isNonUnitalDGAlgebra_zero 𝒜 (R := R)).toAInfinityAlgebra.IsFormal :=
  (isNonUnitalDGAlgebra_zero 𝒜).isFormal_toAInfinityAlgebra_of_differential_eq_zero rfl

end TauCeti
