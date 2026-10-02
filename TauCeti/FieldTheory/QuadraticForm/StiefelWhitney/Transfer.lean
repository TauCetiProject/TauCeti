/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisCohomology.MuTwo.Transfer
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Class
public import TauCeti.LinearAlgebra.QuadraticForm.Transfer.Discriminant

/-!
# The first Stiefel–Whitney class of a transferred line

Let `L/K` be a finite extension of fields in which `2` is invertible, `s : L → K` a nonzero
`K`-linear functional, and `a ∈ Lˣ` with Kummer class `x = (a) ∈ H¹(G_L, 𝔽₂)`. The first
Stiefel–Whitney class of the Scharlau transfer of the line `⟨a⟩` is

```text
w₁(s_*⟨a⟩) = w₁(s_*⟨1⟩) + cor(x),
```

where `cor : H¹(G_L, 𝔽₂) → H¹(G_K, 𝔽₂)` is corestriction along any `K`-embedding of `L` into a
separable closure of `K`. For the trace of a finite separable extension this is the degree-one
part of Kahn's relative Stiefel–Whitney formula for `Tr_*⟨a⟩`.

Since `w₁` is the Kummer class of the discriminant, the formula is the discriminant identity
`d(s_*⟨a⟩) = d(s_*⟨1⟩) · N_{L/K}(a)` (`TauCeti.discr_formClass_scharlauTransfer_smul_sq`) read
through the Kummer isomorphism, together with the law `cor (a) = (N_{L/K} a)`
(`TauCeti.galoisCor_kummerClass`).

## Main results

* `TauCeti.sw1Class_scharlauTransfer_mk_rankOne`: `w₁(s_*⟨a⟩) = w₁(s_*⟨1⟩) + cor (a)` for the
  class-level transfer along a nonzero functional.
* `TauCeti.sw1Class_traceTransfer_mk_rankOne`: `w₁(Tr_*⟨a⟩) = w₁(Tr_*⟨1⟩) + cor (a)` for a
  finite separable extension.
* `TauCeti.sw1Class_formClass_traceTransfer_smul_sq`: the same identity for the twisted trace
  forms `x ↦ Tr_{L/K}(a x²)` and `x ↦ Tr_{L/K}(x²)` on `L` themselves.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. 78 (1984), 223–256, Théorème 2.
-/

public section

noncomputable section

namespace TauCeti

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Invertible (2 : K)] [Invertible (2 : L)] (σ : L →ₐ[K] SeparableClosure K)

/-- **The first Stiefel–Whitney class of a transferred line**: for a nonzero functional
`s : L → K` and `a ∈ Lˣ`, `w₁(s_*⟨a⟩) = w₁(s_*⟨1⟩) + cor (a)`, with corestriction taken along
any `K`-embedding `σ` of `L` into a separable closure of `K`. -/
theorem sw1Class_scharlauTransfer_mk_rankOne (s : L →ₗ[K] K) (hs : s ≠ 0) (a : Lˣ) :
    sw1Class (RegularFormClass.scharlauTransfer s hs
        (Quotient.mk (regularFormSetoid L) ⟨1, fun _ => a⟩)) =
      sw1Class (RegularFormClass.scharlauTransfer s hs 1) + galoisCor K L σ 1 (kummerClass a) := by
  rw [sw1Class_eq_kummerSquareClassEquiv_discr, sw1Class_eq_kummerSquareClassEquiv_discr,
    RegularFormClass.discr_scharlauTransfer_mk_rankOne, map_add,
    kummerSquareClassEquiv_squareClass, galoisCor_kummerClass]

/-- **The relative Stiefel–Whitney formula in degree one, on the trace forms themselves**: for a
finite extension `L/K` and `a ∈ Lˣ`, the first Stiefel–Whitney classes of the regular
forms `x ↦ Tr_{L/K}(a x²)` and `x ↦ Tr_{L/K}(x²)` on `L` differ by `cor (a)`. Regularity of the
two forms is a hypothesis; it forces `L/K` to be separable. -/
theorem sw1Class_formClass_traceTransfer_smul_sq (a : Lˣ)
    (ha : (((a : L) • QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate)
    (h1 : ((QuadraticMap.sq (R := L) (A := L)).traceTransfer K).Nondegenerate) :
    sw1Class (formClass _ ha) = sw1Class (formClass _ h1) + galoisCor K L σ 1 (kummerClass a) := by
  simp only [QuadraticMap.traceTransfer_eq_scharlauTransfer] at ha h1
  rw [sw1Class_eq_kummerSquareClassEquiv_discr, sw1Class_eq_kummerSquareClassEquiv_discr]
  simp only [QuadraticMap.traceTransfer_eq_scharlauTransfer]
  rw [discr_formClass_scharlauTransfer_smul_sq _ a ha h1, map_add,
    kummerSquareClassEquiv_squareClass, galoisCor_kummerClass]

variable [Algebra.IsSeparable K L]

/-- **The relative Stiefel–Whitney formula in degree one**: for a finite separable extension
`L/K` and `a ∈ Lˣ`, `w₁(Tr_*⟨a⟩) = w₁(Tr_*⟨1⟩) + cor (a)`, with corestriction taken along any
`K`-embedding `σ` of `L` into a separable closure of `K`. -/
theorem sw1Class_traceTransfer_mk_rankOne (a : Lˣ) :
    sw1Class (RegularFormClass.traceTransfer K
        (Quotient.mk (regularFormSetoid L) ⟨1, fun _ => a⟩)) =
      sw1Class (RegularFormClass.traceTransfer K (1 : RegularFormClass L)) +
        galoisCor K L σ 1 (kummerClass a) := by
  simp only [RegularFormClass.traceTransfer_eq_scharlauTransfer]
  exact sw1Class_scharlauTransfer_mk_rankOne σ _ _ a

end TauCeti
