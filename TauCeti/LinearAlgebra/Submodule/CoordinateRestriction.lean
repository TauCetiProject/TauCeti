/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Restricting subspaces to base-field coordinates

Let `ι` be a finite index type. For an algebra `S` over `R`, the vectors in `ι → R` whose
coordinatewise images belong to an `S`-submodule `W` form
`(W.restrictScalars R).comap (Pi.algebraMap ι R S)`. A proper `W` gives a proper submodule over `R`:
containing every base-ring vector would force `W` to contain the standard basis over `S`.
For a faithful algebra of commutative rings with `S` a domain,
restriction cannot increase `Module.finrank`, although it can strictly decrease it.

Finite covers by proper subspaces therefore pull back to finite covers by proper subspaces,
without increasing the number of subspaces. This is the linear-algebra step in descent of
exceptional subspaces from a coefficient field to the field of the points.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Remark 7.2.3.
-/

public section

namespace Submodule

variable {ι R S : Type*} [Finite ι] [CommSemiring R] [Semiring S] [Algebra R S]

/-- For a finite index type `ι`, the restriction of an `S`-submodule of `ι → S` to
base-ring coordinates is the whole coordinate module if and only if the original submodule is.
In particular, restriction to base-ring coordinates preserves properness. -/
@[simp]
theorem comap_piAlgebraMap_eq_top_iff (W : Submodule S (ι → S)) :
    (W.restrictScalars R).comap (Pi.algebraMap ι R S) = ⊤ ↔ W = ⊤ := by
  classical
  constructor
  · intro h
    rw [eq_top_iff_forall_basis_mem (Pi.basisFun S ι)]
    intro i
    have hi : Pi.algebraMap ι R S (Pi.basisFun R ι i) ∈ W := by
      simpa only [mem_comap, restrictScalars_mem] using
        (eq_top_iff'.mp h) (Pi.basisFun R ι i)
    have he : Pi.algebraMap ι R S (Pi.basisFun R ι i) = Pi.basisFun S ι i := by
      ext j
      by_cases hj : j = i <;> simp [Pi.algebraMap, Pi.basisFun_apply, hj]
    rwa [he] at hi
  · rintro rfl
    simp

end Submodule

namespace Submodule

variable (R : Type*) {ι S : Type*} [Finite ι] [CommRing R] [CommRing S]
  [Algebra R S] [FaithfulSMul R S] [IsDomain S]

/-- For a finite index type `ι` and a faithful algebra of commutative rings with `S` a domain,
the `R`-finrank of the restriction of `W : Submodule S (ι → S)` to `ι → R` is at most the
`S`-finrank of `W`. In particular, over fields no finiteness assumption on the extension is
needed. -/
theorem finrank_comap_piAlgebraMap_le (W : Submodule S (ι → S)) :
    Module.finrank R ((W.restrictScalars R).comap (Pi.algebraMap ι R S)) ≤
      Module.finrank S W := by
  classical
  let U := (W.restrictScalars R).comap (Pi.algebraMap ι R S)
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := U) le_rfl
  have hR := hv.map' U.subtype U.ker_subtype
  have hmap (x : ι → R) : Pi.algebraMap ι R S x = algebraMap R S ∘ x := rfl
  have hS : LinearIndependent S (fun i ↦ Pi.algebraMap ι R S (v i)) := by
    simpa only [hmap, Submodule.coe_subtype, Function.comp_apply] using
      (linearIndependent_algebraMap_comp_iff (S := S)).mpr hR
  have hmem (i) : Pi.algebraMap ι R S (v i) ∈ W := by
    simpa only [U, mem_comap, restrictScalars_mem] using (v i).property
  have hW : LinearIndependent S (fun i ↦ (⟨Pi.algebraMap ι R S (v i), hmem i⟩ : W)) :=
    hS.codRestrict W hmem
  simpa only [Cardinal.mk_fin, Cardinal.lift_natCast, ← W.finrank_eq_rank,
    Nat.cast_le] using hW.cardinal_lift_le_rank

end Submodule

namespace Finset

variable (R : Type*) {ι S : Type*} [Finite ι] [CommSemiring R] [Semiring S] [Algebra R S]

/-- For a finite index type `ι`, a finite family of proper `S`-submodules of `ι → S` restricts
to a family of proper `R`-submodules of `ι → R`, with the same covered base-ring vectors and no
larger cardinality. Distinct submodules are allowed to have the same restriction. -/
theorem exists_finset_submodule_card_le_and_piAlgebraMap_mem_iff (T : Finset (Submodule S (ι → S)))
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
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem,
    Submodule.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
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
