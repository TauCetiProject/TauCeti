/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Restricting subspaces to base-field coordinates

For an algebra `S` over `R`, the vectors over `R` whose coordinatewise images belong to an
`S`-submodule `W` form `(W.restrictScalars R).comap (Pi.algebraMap ι R S)`. A proper `W` gives
a proper submodule over `R`: containing every base-ring vector would force `W` to contain the
standard basis over `S`. Over fields, restriction cannot increase dimension, although it can
strictly decrease it.

Finite covers by proper subspaces therefore pull back to finite covers by proper subspaces,
without increasing the number of subspaces. This is the linear-algebra step in descent of
exceptional subspaces from a coefficient field to the field of the points.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Remark 7.2.3.
-/

public section

namespace Submodule

variable {ι R S : Type*} [Finite ι] [CommSemiring R] [Semiring S] [Algebra R S]

/-- An `S`-submodule containing all vectors with coordinates in the base ring is the whole
coordinate module. In particular, restriction to base-ring coordinates preserves properness. -/
@[simp]
theorem comap_piAlgebraMap_eq_top_iff (W : Submodule S (ι → S)) :
    (W.restrictScalars R).comap (Pi.algebraMap ι R S) = ⊤ ↔ W = ⊤ := by
  classical
  constructor
  · intro h
    rw [eq_top_iff_forall_basis_mem (Pi.basisFun S ι)]
    intro i
    have hi : Pi.algebraMap ι R S (Pi.basisFun R ι i) ∈ W :=
      (eq_top_iff'.mp h) (Pi.basisFun R ι i)
    have he : Pi.algebraMap ι R S (Pi.basisFun R ι i) = Pi.basisFun S ι i := by
      ext j
      by_cases hj : j = i <;> simp [Pi.algebraMap, Pi.basisFun_apply, hj]
    rwa [he] at hi
  · rintro rfl
    simp

end Submodule

namespace Submodule

variable {ι K L : Type*} [Finite ι] [Field K] [Field L] [Algebra K L]

/-- The dimension of the base-field vectors in a subspace is at most the dimension of that
subspace over the larger field. No finiteness assumption on the field extension is needed. -/
theorem finrank_comap_piAlgebraMap_le (W : Submodule L (ι → L)) :
    Module.finrank K ((W.restrictScalars K).comap (Pi.algebraMap ι K L)) ≤
      Module.finrank L W := by
  classical
  let U := (W.restrictScalars K).comap (Pi.algebraMap ι K L)
  let b := Module.finBasis K U
  have hb := b.linearIndependent.map' U.subtype U.ker_subtype
  have hL := (linearIndependent_algebraMap_comp_iff (S := L)).mpr hb
  let v (i : Fin (Module.finrank K U)) : W :=
    ⟨Pi.algebraMap ι K L (b i), (b i).property⟩
  have hv : LinearIndependent L v := hL.of_comp W.subtype
  simpa using hv.fintype_card_le_finrank

end Submodule

namespace Finset

variable {ι R S : Type*} [Finite ι] [CommSemiring R] [Semiring S] [Algebra R S]

/-- A finite family of proper submodules over an algebra restricts to a family of proper
submodules over the base ring, with the same covered base-ring vectors and no larger cardinality.
Distinct submodules are allowed to have the same restriction. -/
theorem exists_submodule_cover_of_piAlgebraMap (T : Finset (Submodule S (ι → S)))
    (hT : ∀ W ∈ T, W ≠ ⊤) :
    ∃ T₀ : Finset (Submodule R (ι → R)), T₀.card ≤ T.card ∧
      (∀ U ∈ T₀, U ≠ ⊤) ∧ ∀ x : ι → R,
        (∃ W ∈ T, Pi.algebraMap ι R S x ∈ W) ↔ ∃ U ∈ T₀, x ∈ U := by
  classical
  refine ⟨T.image (fun W ↦ (W.restrictScalars R).comap (Pi.algebraMap ι R S)),
    card_image_le, ?_, ?_⟩
  · intro U hU
    obtain ⟨W, hW, rfl⟩ := mem_image.mp hU
    simpa using hT W hW
  · intro x
    simp

end Finset

-- Restriction can lose dimension: this complex line has no nonzero real vector.
example :
    ((Submodule.span ℂ {![1, Complex.I]}).restrictScalars ℝ).comap
      (Pi.algebraMap (Fin 2) ℝ ℂ) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
  have h₀ := congrArg (fun y : Fin 2 → ℂ ↦ (y 0).im) hc
  have h₁ := congrArg (fun y : Fin 2 → ℂ ↦ (y 1).im) hc
  have hc₀ : c = 0 := by
    apply Complex.ext
    · simpa [Pi.algebraMap] using h₁
    · simpa [Pi.algebraMap] using h₀
  have hx₀ := hc₀ ▸ hc
  ext j
  apply Complex.ofReal_injective
  simpa [Pi.algebraMap] using (congrFun hx₀ j).symm
