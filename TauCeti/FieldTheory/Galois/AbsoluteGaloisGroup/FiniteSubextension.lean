/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# Transporting finite Galois subextensions between separable closures

Let `L/K` be embedded in `Kˢ` by `σ`, and let `E/L` be embedded in `Kˢ` compatibly with `σ`.
The chosen identification `separableClosureRingEquiv K L σ : Lˢ ≃+* Kˢ` transports this
embedding to an `L`-embedding in `Lˢ`. If `E/L` is finite and normal, its image is a finite
Galois subextension of `Lˢ/L`, with an algebra equivalence recording the ambient embedding.

This supplies finite fields and compatible coefficient maps for comparing finite cocycle
restriction with restriction on absolute Galois cohomology. In particular, a finite Galois
extension of `K` containing the image of `L` can be read inside the separable closure of `L`.
No normality of `L/K` is needed.

## References

* J.-P. Serre, *Local Fields*, Chapter X, §5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter VI, §1.
-/

public section

noncomputable section

namespace AlgHom

open TauCeti

universe u v w

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
  {E : Type w} [Field E] [Algebra K E] [Algebra L E]

/-- Transport a compatible embedding of `E` into `Kˢ` to an `L`-embedding into `Lˢ`, using
the chosen identification of separable closures extending `σ`. -/
def liftToSeparableClosure (σ : L →ₐ[K] SeparableClosure K)
    (ι : E →ₐ[K] SeparableClosure K) (hι : ∀ x : L, ι (algebraMap L E x) = σ x) :
    E →ₐ[L] SeparableClosure L :=
  { (separableClosureRingEquiv K L σ).symm.toRingHom.comp ι.toRingHom with
    commutes' x := by
      simp [hι] }

/-- The transported embedding is the original embedding followed by the inverse
identification of separable closures. -/
theorem liftToSeparableClosure_apply (σ : L →ₐ[K] SeparableClosure K)
    (ι : E →ₐ[K] SeparableClosure K) (hι : ∀ x : L, ι (algebraMap L E x) = σ x) (y : E) :
    σ.liftToSeparableClosure ι hι y = (separableClosureRingEquiv K L σ).symm (ι y) :=
  (rfl)

/-- The two ambient embeddings agree through the identification of separable closures. -/
@[simp]
theorem separableClosureRingEquiv_liftToSeparableClosure
    (σ : L →ₐ[K] SeparableClosure K) (ι : E →ₐ[K] SeparableClosure K)
    (hι : ∀ x : L, ι (algebraMap L E x) = σ x) (y : E) :
    separableClosureRingEquiv K L σ (σ.liftToSeparableClosure ι hι y) = ι y := by
  rw [liftToSeparableClosure_apply, RingEquiv.apply_symm_apply]

/-- A finite normal extension embedded compatibly in `Kˢ` is isomorphic to a finite Galois
subextension of `Lˢ/L`. The equivalence preserves the specified embedding into `Kˢ` through
the chosen identification of separable closures. -/
theorem exists_finiteGalois_subextension_equiv [FiniteDimensional L E] [Normal L E]
    (σ : L →ₐ[K] SeparableClosure K) (ι : E →ₐ[K] SeparableClosure K)
    (hι : ∀ x : L, ι (algebraMap L E x) = σ x) :
    ∃ M : IntermediateField L (SeparableClosure L),
      FiniteDimensional L M ∧ IsGalois L M ∧
        ∃ e : E ≃ₐ[L] M, ∀ y : E,
          separableClosureRingEquiv K L σ (e y : SeparableClosure L) = ι y := by
  let f := σ.liftToSeparableClosure ι hι
  have : FiniteDimensional L f.fieldRange := f.toLinearMap.finiteDimensional_range
  refine ⟨f.fieldRange, inferInstance, IsGalois.mk, f.equivFieldRange, fun y ↦ ?_⟩
  rw [equivFieldRange_apply_coe]
  exact separableClosureRingEquiv_liftToSeparableClosure σ ι hι y

end AlgHom
