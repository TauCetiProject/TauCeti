/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.Geometry.Variational.PolynomialJet.Basic

/-!
# Semilinear maps of field generators and conjugation of polynomial jets

The field coordinates `uᵃ_I` of `TauCeti.PolynomialJet R ι α` are the jets of a basis of the
module of field generators `α →₀ R`: a generator `v` has the jet coordinate
`PolynomialJet.fieldJet I v = ∑ₐ vₐ uᵃ_I` at the multi-index `I`.

A map `f : (α →₀ R) →ₛₗ[σ] (β →₀ S)` of field generators, semilinear over a ring map
`σ : R →+* S`, extends to the ring map `PolynomialJet.fieldMap f` of polynomial jets which applies
`σ` to the coefficients, fixes the base coordinates, and sends `uᵃ_I` to the jet coordinate of
`f eₐ` at `I`. Linear field redefinitions (`σ = RingHom.id R`), complexification of real fields
(`σ = algebraMap ℝ ℂ`) and conjugations of complex fields (`σ = starRingEnd R`) are the main
instances. These extensions:

* commute with all total derivatives (`PolynomialJet.totalDeriv_fieldMap`) and preserve the
  finite stages (`PolynomialJet.fieldMap_mem_stage`);
* are functorial (`PolynomialJet.fieldMap_id`, `PolynomialJet.fieldMap_comp`), so an involutive
  conjugation of the field generators extends to an involution of polynomial jets
  (`PolynomialJet.fieldMap_involutive`);
* are compatible with field evaluations (`PolynomialJet.aeval_fieldMap`): evaluating the image
  of an expression on one field configuration is evaluating the expression on a related one.

For a conjugation `c` of the field generators, a field configuration with values in a
commutative star algebra is *real* when its base coordinates are self-adjoint and the
evaluation of `c eₐ` is the conjugate of the value of `uᵃ_I`. Real field configurations take the
conjugate of an expression to the conjugate of its value (`PolynomialJet.aeval_fieldMap_star`),
so expressions fixed by the conjugation evaluate to self-adjoint values
(`PolynomialJet.isSelfAdjoint_aeval_of_fieldMap_eq_self`). Two instances are real fields, with `c`
conjugating coefficients, and conjugate pairs (a field `ψ` together with its conjugate field), with
`c` also exchanging their generators (`PolynomialJet.aeval_fieldMap_mapDomain_star`).

The coordinatewise conjugation of the field generators extends to the coefficientwise
conjugation `MvPolynomial.map (starRingEnd R)` (`PolynomialJet.fieldMap_mapRange`). Over `ℂ`, the
jets it fixes are exactly the complexifications of real polynomial jets
(`MvPolynomial.map_starRingEnd_eq_self_iff`).

## References

* I. M. Anderson, *The Variational Bicomplex* (1989), Chapter 1, §A, for jet coordinates and
  total derivatives.
* R. E. Borcherds, *Quantum Field Theory*, lecture notes (2001), p.35, the source model for real
  fields versus conjugate-paired fields (a complex field together with its conjugate field).
-/

public section

namespace TauCeti

namespace PolynomialJet

open MvPolynomial

noncomputable section

variable {R S T ι α β γ : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]

/-! ### Jet coordinates of field generators -/

/-- The jet coordinate `∑ₐ vₐ uᵃ_I` at the multi-index `I` of a field generator `v`. -/
def fieldJet (I : ι →₀ ℕ) : (α →₀ R) →ₗ[R] PolynomialJet R ι α :=
  Finsupp.linearCombination R fun a ↦ X (Sum.inr (a, I))

theorem fieldJet_apply (I : ι →₀ ℕ) (v : α →₀ R) :
    fieldJet I v = v.sum fun a r ↦ C r * X (Sum.inr (a, I)) := by
  simp [fieldJet, Finsupp.linearCombination_apply, smul_eq_C_mul]

@[simp]
theorem fieldJet_single (I : ι →₀ ℕ) (a : α) (r : R) :
    fieldJet I (Finsupp.single a r) = C r * X (Sum.inr (a, I)) := by
  simp [fieldJet, smul_eq_C_mul]

/-- Total differentiation shifts the jet coordinate of a field generator. -/
@[simp]
theorem totalDeriv_fieldJet (i : ι) (I : ι →₀ ℕ) (v : α →₀ R) :
    totalDeriv i (fieldJet I v) = fieldJet (I + Finsupp.single i 1) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single a r => simp

theorem fieldJet_mem_stage {r : ℕ} {I : ι →₀ ℕ} (hI : I.degree ≤ r) (v : α →₀ R) :
    fieldJet I v ∈ stage R ι α r := by
  rw [fieldJet_apply]
  exact sum_mem fun a _ ↦ mul_mem ((stage R ι α r).algebraMap_mem _)
    (X_field_mem_stage r a I hI)

/-! ### Extension of semilinear maps of field generators -/

variable {σ : R →+* S} {τ : S →+* T} {ρ : R →+* T}

/-- The extension of a semilinear map of field generators to polynomial jets: it applies `σ` to
the coefficients, fixes the base coordinates and sends `uᵃ_I` to the jet coordinate of `f eₐ`
at `I`. -/
def fieldMap (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) : PolynomialJet R ι α →+* PolynomialJet S ι β :=
  eval₂Hom (C.comp σ)
    (Sum.elim (fun j ↦ X (Sum.inl j)) fun aI ↦ fieldJet aI.2 (f (Finsupp.single aI.1 1)))

@[simp]
theorem fieldMap_C (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (r : R) :
    fieldMap (ι := ι) f (C r) = C (σ r) := by
  simp [fieldMap]

@[simp]
theorem fieldMap_X_base (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (j : ι) :
    fieldMap f (X (Sum.inl j)) = X (Sum.inl j) := by
  simp [fieldMap]

@[simp]
theorem fieldMap_X_field (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (a : α) (I : ι →₀ ℕ) :
    fieldMap f (X (Sum.inr (a, I))) = fieldJet I (f (Finsupp.single a 1)) := by
  simp [fieldMap]

/-- The extension is `σ`-semilinear. -/
@[simp]
theorem fieldMap_smul (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (r : R) (p : PolynomialJet R ι α) :
    fieldMap f (r • p) = σ r • fieldMap f p := by
  rw [smul_eq_C_mul, map_mul, fieldMap_C, ← smul_eq_C_mul]

/-- The extension takes the jet coordinate of a generator `v` to the jet coordinate of `f v`. -/
@[simp]
theorem fieldMap_fieldJet (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (I : ι →₀ ℕ) (v : α →₀ R) :
    fieldMap f (fieldJet I v) = fieldJet I (f v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp [hv, hw]
  | single a r =>
    -- Pull the scalar `r` out of both sides; the unit generator case is then `simp`.
    rw [← Finsupp.smul_single_one a r, map_smul, fieldMap_smul, map_smulₛₗ]
    simp

/-- The extensions commute with every total derivative. -/
@[simp]
theorem totalDeriv_fieldMap (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (i : ι) (p : PolynomialJet R ι α) :
    totalDeriv i (fieldMap f p) = fieldMap f (totalDeriv i p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    rcases v with j | ⟨a, I⟩
    · simp [Derivation.leibniz, hp, apply_ite]
    · simp [Derivation.leibniz, hp]

/-- The extensions preserve each finite stage. -/
theorem fieldMap_mem_stage (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) {r : ℕ} {p : PolynomialJet R ι α}
    (hp : p ∈ stage R ι α r) : fieldMap f p ∈ stage S ι β r := by
  -- `stage` is the subalgebra generated by the base coordinates and the field coordinates of
  -- order at most `r`; induct over that generation. The body of `stage` is not exposed outside
  -- its module, so its membership is restated as an adjoin through `mem_stage_iff`.
  have hp' : p ∈ Algebra.adjoin R
      (X '' {v | Sum.elim (fun _ ↦ True) (fun aI ↦ aI.2.degree ≤ r) v}) := by
    rw [← supported_eq_adjoin_X, mem_supported]
    rintro (j | ⟨a, I⟩) hv
    · trivial
    · exact (mem_stage_iff p r).1 hp a I hv
  clear hp
  induction hp' using Algebra.adjoin_induction with
  | mem v hv =>
    obtain ⟨j | ⟨a, I⟩, hj, rfl⟩ := hv
    · simp
    · rw [fieldMap_X_field]
      exact fieldJet_mem_stage hj _
  | algebraMap c => simpa using (stage S ι β r).algebraMap_mem (σ c)
  | add p q _ _ hp hq => simpa using add_mem hp hq
  | mul p q _ _ hp hq => simpa using mul_mem hp hq

@[simp]
theorem fieldMap_id : fieldMap (ι := ι) (LinearMap.id : (α →₀ R) →ₗ[R] α →₀ R) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · simp
  · rintro (j | ⟨a, I⟩) <;> simp

/-- The extension of a composite is the composite of the extensions. -/
theorem fieldMap_comp [RingHomCompTriple σ τ ρ] (g : (β →₀ S) →ₛₗ[τ] (γ →₀ T))
    (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) :
    fieldMap (ι := ι) (g.comp f) = (fieldMap g).comp (fieldMap f) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [RingHomCompTriple.comp_apply]
  · rintro (j | ⟨a, I⟩) <;> simp

/-- The extension of a composite is the composite of the extensions, applied to an element. -/
@[simp]
theorem fieldMap_fieldMap [RingHomCompTriple σ τ ρ] (g : (β →₀ S) →ₛₗ[τ] (γ →₀ T))
    (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (p : PolynomialJet R ι α) :
    fieldMap g (fieldMap f p) = fieldMap (g.comp f) p := by
  rw [fieldMap_comp, RingHom.comp_apply]

/-- A left inverse of a semilinear map of field generators extends to a left inverse of its
extension. -/
theorem fieldMap_leftInverse {σ' : S →+* R} [RingHomCompTriple σ σ' (RingHom.id R)]
    {f : (α →₀ R) →ₛₗ[σ] (β →₀ S)} {g : (β →₀ S) →ₛₗ[σ'] (α →₀ R)}
    (h : Function.LeftInverse g f) :
    Function.LeftInverse (fieldMap (ι := ι) g) (fieldMap f) := by
  intro p
  have hgf : g.comp f = LinearMap.id := LinearMap.ext h
  rw [fieldMap_fieldMap, hgf, fieldMap_id, RingHom.id_apply]

/-- An involutive conjugation of field generators extends to an involution of polynomial
jets. -/
theorem fieldMap_involutive [StarRing R] {c : (α →₀ R) →ₛₗ[starRingEnd R] (α →₀ R)}
    (hc : Function.Involutive c) : Function.Involutive (fieldMap (ι := ι) c) :=
  fieldMap_leftInverse hc

/-- Applying a ring map coordinatewise to the field generators extends to applying it to the
coefficients of polynomial jets. -/
@[simp]
theorem fieldMap_mapRange (σ : R →+* S) :
    fieldMap (ι := ι) (Finsupp.mapRange.linearMap σ.toSemilinearMap : (α →₀ R) →ₛₗ[σ] α →₀ S) =
      map σ := by
  apply MvPolynomial.ringHom_ext
  · simp
  · rintro (j | ⟨a, I⟩) <;> simp

/-! ### Field evaluations -/

section Evaluation

variable {A B : Type*} [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra S B]

omit [CommSemiring S] in
@[simp]
theorem aeval_fieldJet (w : ι ⊕ α × (ι →₀ ℕ) → A) (I : ι →₀ ℕ) (v : α →₀ R) :
    aeval w (fieldJet I v) = Finsupp.linearCombination R (fun a ↦ w (Sum.inr (a, I))) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ h₁ h₂ => simp [h₁, h₂]
  | single a r => simp [Algebra.smul_def]

/-- Evaluating the image of an expression under the extension of `f` on a field configuration
`(y, v)` is applying `κ` to the value of the expression on `(x, u)`, provided `κ` is compatible
with `σ` on scalars, `y = κ ∘ x`, and on each generator the evaluation of `f eₐ` under `v` is the
image under `κ` of the value of `uᵃ`. -/
theorem aeval_fieldMap (f : (α →₀ R) →ₛₗ[σ] (β →₀ S)) (κ : A →+* B)
    (hκ : ∀ r, κ (algebraMap R A r) = algebraMap S B (σ r)) (x : ι → A)
    (u : α → (ι →₀ ℕ) → A) (v : β → (ι →₀ ℕ) → B)
    (huv : ∀ a I, Finsupp.linearCombination S (fun b ↦ v b I) (f (Finsupp.single a 1)) =
      κ (u a I))
    (p : PolynomialJet R ι α) :
    aeval (Sum.elim (κ ∘ x) fun bI ↦ v bI.1 bI.2) (fieldMap f p) =
      κ (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) := by
  have h : RingHom.comp (aeval (Sum.elim (κ ∘ x) fun bI ↦ v bI.1 bI.2) :
        PolynomialJet S ι β →ₐ[S] B).toRingHom (fieldMap f) =
      κ.comp (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) : PolynomialJet R ι α →ₐ[R] A) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [hκ]
    · rintro (j | ⟨a, I⟩) <;> simp [huv]
  exact congrArg (fun φ : PolynomialJet R ι α →+* B ↦ φ p) h

/-- On a real field configuration for a conjugation `c`, the conjugate of an expression
evaluates to the conjugate of its value. The configuration is real when the base coordinates
are self-adjoint and the evaluation of `c eₐ` is the conjugate of the value of each `uᵃ_I`. -/
theorem aeval_fieldMap_star [StarRing R] [StarRing A] [StarModule R A]
    (c : (α →₀ R) →ₛₗ[starRingEnd R] (α →₀ R)) (x : ι → A) (hx : ∀ j, star (x j) = x j)
    (u : α → (ι →₀ ℕ) → A)
    (hu : ∀ a I, Finsupp.linearCombination R (fun b ↦ u b I) (c (Finsupp.single a 1)) =
      star (u a I))
    (p : PolynomialJet R ι α) :
    aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) (fieldMap c p) =
      star (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) := by
  have hx' : (starRingEnd A) ∘ x = x := funext fun j ↦ (starRingEnd_apply _).trans (hx j)
  have h := aeval_fieldMap c (starRingEnd A)
    (fun r ↦ by rw [starRingEnd_apply, starRingEnd_apply, algebraMap_star_comm]) x u u
    (fun a I ↦ (hu a I).trans (starRingEnd_apply _).symm) p
  rw [hx', starRingEnd_apply] at h
  exact h

/-- On a real field configuration, an expression fixed by the conjugation evaluates to a
self-adjoint value. -/
theorem isSelfAdjoint_aeval_of_fieldMap_eq_self [StarRing R] [StarRing A] [StarModule R A]
    (c : (α →₀ R) →ₛₗ[starRingEnd R] (α →₀ R)) (x : ι → A) (hx : ∀ j, star (x j) = x j)
    (u : α → (ι →₀ ℕ) → A)
    (hu : ∀ a I, Finsupp.linearCombination R (fun b ↦ u b I) (c (Finsupp.single a 1)) =
      star (u a I))
    {p : PolynomialJet R ι α} (hp : fieldMap c p = p) :
    IsSelfAdjoint (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) := by
  rw [IsSelfAdjoint, ← aeval_fieldMap_star c x hx u hu, hp]

/-- Conjugate-paired fields: let the conjugation of field generators conjugate coefficients and
relabel generators by `e`, as for a field `ψ` and its conjugate field exchanged by `e`, or a real
field fixed by `e`. If each field `u (e a)` is the conjugate of `u a`, the conjugate of an
expression evaluates to the conjugate of its value. -/
theorem aeval_fieldMap_mapDomain_star [StarRing R] [StarRing A] [StarModule R A] (e : α → α)
    (x : ι → A) (hx : ∀ j, star (x j) = x j) (u : α → (ι →₀ ℕ) → A)
    (hu : ∀ a I, u (e a) I = star (u a I)) (p : PolynomialJet R ι α) :
    aeval (Sum.elim x fun aI ↦ u aI.1 aI.2)
        (fieldMap ((Finsupp.lmapDomain R R e).comp
          (Finsupp.mapRange.linearMap (starRingEnd R).toSemilinearMap)) p) =
      star (aeval (Sum.elim x fun aI ↦ u aI.1 aI.2) p) :=
  aeval_fieldMap_star _ x hx u (fun a I ↦ by simp [hu]) p

end Evaluation

end

end PolynomialJet

end TauCeti
