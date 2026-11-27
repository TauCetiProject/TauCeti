/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
public import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# Exact C*-algebras

A C*-algebra `A` is **exact** (`TauCeti.CStarAlgebra.IsExact`) when tensoring every closed-ideal
sequence `0 → J → B → B/J → 0` of C*-algebras with `A ⊗min −` leaves it exact (Blackadar
II.9.6.6): the sequence

`0 → A ⊗min J → A ⊗min B → A ⊗min (B/J) → 0`

of the star homomorphisms `TauCeti.MinTensorProduct.map` of the inclusion `J → B` and of the
quotient map `B → B/J` is exact. Two of the three exactness conditions hold for every `A`: the
first map is injective, since the minimal tensor product preserves injectivity
(`TauCeti.MinTensorProduct.map_injective` with `TwoSidedIdeal.starAlgHom_injective`), and the last
one is surjective (`TauCeti.MinTensorProduct.map_surjective` with
`TwoSidedIdeal.Quotient.mkStarAlgHom_surjective`). The composite is zero, so the image of
`A ⊗min J`, which is the closure of the image of `A ⊗[ℂ] J`
(`TauCeti.MinTensorProduct.range_map`), always lies in the kernel of `A ⊗min B → A ⊗min (B/J)`
(`TauCeti.MinTensorProduct.map_mkStarAlgHom_map_starAlgHom_eq_zero`). Exactness is therefore the
remaining inclusion, of the kernel in the image (`TauCeti.CStarAlgebra.isExact_iff`).

The algebras `B` are quantified over a fixed universe `w`, a universe parameter of
`TauCeti.CStarAlgebra.IsExact`.

## Main declarations

* `TauCeti.CStarAlgebra.IsExact`: exactness of `A ⊗min −` on closed-ideal sequences.

## Main statements

* `TauCeti.CStarAlgebra.isExact_iff`: the kernel formulation, exactness as the inclusion of the
  kernel in the image.
* `TauCeti.CStarAlgebra.IsExact.of_starAlgEquiv`: exactness is invariant under star isomorphism.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.6.6.
-/

public section

noncomputable section

open TensorProduct
open scoped CStarAlgebra

universe u w

namespace TauCeti

namespace MinTensorProduct

variable {A B A' : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra A']

section Ideal

variable (J : TwoSidedIdeal B) [IsClosed (J : Set B)]

open TwoSidedIdeal.Quotient (mkStarAlgHom)

/-- The composite `A ⊗min J → A ⊗min B → A ⊗min (B/J)` is zero: the image of `A ⊗min J` lies
in the kernel of the quotient map. -/
@[simp]
theorem map_mkStarAlgHom_map_starAlgHom_eq_zero (u : MinTensorProduct A J) :
    map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J)
      (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom u) = 0 := by
  have h : (mkStarAlgHom J).comp J.starAlgHom = 0 :=
    NonUnitalStarAlgHom.ext fun x ↦ by
      simp [TwoSidedIdeal.Quotient.eq_zero_iff_mem]
  rw [MinTensorProduct.map_map, h, map_zero_right, NonUnitalStarAlgHom.zero_apply]

end Ideal

end MinTensorProduct

namespace CStarAlgebra

open MinTensorProduct TwoSidedIdeal.Quotient

/-- A C*-algebra `A` is **exact** when for every C*-algebra `B` (in the universe `w`) and every
closed two-sided ideal `J` of `B`, the sequence `A ⊗min J → A ⊗min B → A ⊗min (B/J)` induced by
the inclusion of `J` and the quotient map is exact. The first map is always injective and the
second always surjective (`TauCeti.MinTensorProduct.map_injective`,
`TauCeti.MinTensorProduct.map_surjective`), so this is exactness of the whole
sequence `0 → A ⊗min J → A ⊗min B → A ⊗min (B/J) → 0`. -/
class IsExact.{w', u'} (A : Type u') [NonUnitalCStarAlgebra A] : Prop where
  /-- Tensoring with `A` preserves exactness of closed-ideal sequences. -/
  exact_map : ∀ (B : Type w') [NonUnitalCStarAlgebra B] (J : TwoSidedIdeal B)
    [IsClosed (J : Set B)], Function.Exact (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom)
      (map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J))

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **The kernel formulation of exactness**: since the image of `A ⊗min J` always lies in the
kernel of `A ⊗min B → A ⊗min (B/J)`, `A` is exact when every element of that kernel comes from
`A ⊗min J`. -/
theorem isExact_iff : IsExact.{w} A ↔
    ∀ (B : Type w) [NonUnitalCStarAlgebra B] (J : TwoSidedIdeal B) [IsClosed (J : Set B)]
      (u : MinTensorProduct A B), map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J) u = 0 →
        u ∈ Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom) := by
  refine ⟨fun h B _ J _ u hu ↦ (h.exact_map B J u).1 hu, fun h ↦ ⟨fun B _ J _ ↦
    Function.Exact.of_comp_of_mem_range (funext (map_mkStarAlgHom_map_starAlgHom_eq_zero J))
      (h B J)⟩⟩

/-- **Exactness is invariant under star isomorphism.** -/
theorem IsExact.of_starAlgEquiv {A' : Type*} [NonUnitalCStarAlgebra A'] (e : A ≃⋆ₐ[ℂ] A')
    [IsExact.{w} A] : IsExact.{w} A' := by
  refine isExact_iff.2 fun B _ J _ u hu ↦ ?_
  have hu' : map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J)
      (map e.symm.toNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ B) u) = 0 := by
    simpa [MinTensorProduct.map_map] using
      congrArg (map e.symm.toNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ (B ⧸ J))) hu
  obtain ⟨v, hv⟩ := (IsExact.exact_map (A := A) B J _).1 hu'
  refine ⟨map e.toNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ J) v, ?_⟩
  calc _ = map e.toNonUnitalStarAlgHom (NonUnitalStarAlgHom.id ℂ B)
          (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom v) := by
        simp [MinTensorProduct.map_map]
    _ = u := by rw [hv]; simpa using map_map_symm e (StarAlgEquiv.refl ℂ B) u

end CStarAlgebra

end TauCeti
