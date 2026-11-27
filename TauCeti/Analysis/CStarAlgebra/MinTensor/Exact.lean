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
(`TauCeti.MinTensorProduct.map_starAlgHom_injective`), and the last one is surjective
(`TauCeti.MinTensorProduct.map_mkStarAlgHom_surjective`). The composite is zero, so the image of
`A ⊗min J`, which is the closure of the image of `A ⊗[ℂ] J`
(`TauCeti.MinTensorProduct.range_map`), always lies in the kernel of `A ⊗min B → A ⊗min (B/J)`
(`TauCeti.MinTensorProduct.map_mkStarAlgHom_map_starAlgHom`). Exactness is therefore the remaining
inclusion, of the kernel in the image (`TauCeti.CStarAlgebra.isExact_iff`).

The algebras `B` are quantified over a fixed universe `w`, a universe parameter of
`TauCeti.CStarAlgebra.IsExact`.

## Main declarations

* `TauCeti.CStarAlgebra.IsExact`: exactness of `A ⊗min −` on closed-ideal sequences.

## Main statements

* `TauCeti.MinTensorProduct.map_surjective`: `map φ ψ` is surjective for surjective `φ`, `ψ`.
* `TauCeti.MinTensorProduct.range_map`: the range of `map φ ψ` is the closure of the image of
  the algebraic tensor product.
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

open CStarTensorProduct
open Algebra.TensorProduct (mapNonUnitalStarAlgHom coe_mapNonUnitalStarAlgHom)

variable {A B A' B' A'' B'' : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B'] [NonUnitalCStarAlgebra A'']
  [NonUnitalCStarAlgebra B'']

/-- Composition of the maps of minimal tensor products, elementwise. -/
theorem map_map (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') (u : MinTensorProduct A B) :
    map φ' ψ' (map φ ψ u) = map (φ'.comp φ) (ψ'.comp ψ) u := by
  rw [map_comp, NonUnitalStarAlgHom.comp_apply]

/-- `map φ 0 = 0`. -/
@[simp]
theorem map_zero_right (φ : A →⋆ₙₐ[ℂ] A') :
    map φ (0 : B →⋆ₙₐ[ℂ] B') = 0 :=
  starAlgHom_ext fun a b ↦ by simp

/-- The range of `map φ ψ` is the closure of the image of `A ⊗[ℂ] B`, that is, of
`φ(A) ⊗ ψ(B)`. -/
theorem range_map (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    Set.range (map φ ψ) =
      closure (Set.range fun x ↦ of (minCStarTensorNorm A' B') (mapNonUnitalStarAlgHom φ ψ x)) := by
  refine subset_antisymm ?_ <| closure_minimal ?_ (map φ ψ).isClosed_setRange
  · have hc : Continuous (map φ ψ) := map_continuous _
    rw [← Set.image_univ, ← denseRange_of.closure_range]
    refine (image_closure_subset_closure_image hc).trans <|
      closure_mono ?_
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (map_of φ ψ x).symm⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨of _ x, map_of φ ψ x⟩

/-- For surjective `φ` and `ψ`, `map φ ψ` is surjective. -/
theorem map_surjective {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Surjective φ)
    (hψ : Function.Surjective ψ) : Function.Surjective (map φ ψ) := by
  have h : Function.Surjective (mapNonUnitalStarAlgHom φ ψ) := by
    rw [coe_mapNonUnitalStarAlgHom]
    exact TensorProduct.map_surjective hφ hψ
  have hr : (Set.range fun x ↦ of (minCStarTensorNorm A' B') (mapNonUnitalStarAlgHom φ ψ x)) =
      Set.range (of (minCStarTensorNorm A' B')) :=
    h.range_comp (of _)
  rw [← Set.range_eq_univ, range_map, hr, denseRange_of.closure_range]

section Ideal

variable (J : TwoSidedIdeal B) [IsClosed (J : Set B)]

open TwoSidedIdeal.Quotient (mkStarAlgHom mkStarAlgHom_surjective)

/-- The inclusion of a closed ideal `J` of `B` induces an injective map
`A ⊗min J → A ⊗min B`. -/
theorem map_starAlgHom_injective (φ : A →⋆ₙₐ[ℂ] A') (hφ : Function.Injective φ) :
    Function.Injective (map φ J.starAlgHom) :=
  map_injective hφ J.starAlgHom_injective

/-- The quotient map `B → B/J` induces a surjective map `A ⊗min B → A ⊗min (B/J)`. -/
theorem map_mkStarAlgHom_surjective (φ : A →⋆ₙₐ[ℂ] A') (hφ : Function.Surjective φ) :
    Function.Surjective (map φ (mkStarAlgHom J)) :=
  map_surjective hφ (mkStarAlgHom_surjective J)

/-- The composite `A ⊗min J → A ⊗min B → A ⊗min (B/J)` is zero: the image of `A ⊗min J` lies
in the kernel of the quotient map. -/
@[simp]
theorem map_mkStarAlgHom_map_starAlgHom (u : MinTensorProduct A J) :
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
second always surjective (`TauCeti.MinTensorProduct.map_starAlgHom_injective`,
`TauCeti.MinTensorProduct.map_mkStarAlgHom_surjective`), so this is exactness of the whole
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
  refine ⟨fun h B _ J _ u hu ↦ (h.exact_map B J u).1 hu, fun h ↦ ⟨fun B _ J _ u ↦
    ⟨h B J u, ?_⟩⟩⟩
  rintro ⟨v, rfl⟩
  exact map_mkStarAlgHom_map_starAlgHom J v

/-- In an exact `A`, every element of the kernel of `A ⊗min B → A ⊗min (B/J)` comes from
`A ⊗min J`. -/
theorem IsExact.mem_range [IsExact.{w} A] {B : Type w} [NonUnitalCStarAlgebra B]
    (J : TwoSidedIdeal B) [IsClosed (J : Set B)] {u : MinTensorProduct A B}
    (hu : map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J) u = 0) :
    u ∈ Set.range (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom) :=
  isExact_iff.1 ‹_› B J u hu

/-- **Exactness is invariant under star isomorphism.** -/
theorem IsExact.of_starAlgEquiv {A' : Type*} [NonUnitalCStarAlgebra A'] (e : A ≃⋆ₐ[ℂ] A')
    [IsExact.{w} A] : IsExact.{w} A' := by
  refine isExact_iff.2 fun B _ J _ u hu ↦ ?_
  let f : A →⋆ₙₐ[ℂ] A' := e.toNonUnitalStarAlgHom
  let g : A' →⋆ₙₐ[ℂ] A := e.symm.toNonUnitalStarAlgHom
  have hfg : f.comp g = NonUnitalStarAlgHom.id ℂ A' := NonUnitalStarAlgHom.ext fun x ↦ by
    simp [f, g]
  have hu' : map (NonUnitalStarAlgHom.id ℂ A) (mkStarAlgHom J)
      (map g (NonUnitalStarAlgHom.id ℂ B) u) = 0 := by
    calc _ = map g (mkStarAlgHom J) u := by
          rw [MinTensorProduct.map_map, NonUnitalStarAlgHom.id_comp,
            NonUnitalStarAlgHom.comp_id]
      _ = map g (NonUnitalStarAlgHom.id ℂ (B ⧸ J))
            (map (NonUnitalStarAlgHom.id ℂ A') (mkStarAlgHom J) u) := by
          rw [MinTensorProduct.map_map, NonUnitalStarAlgHom.id_comp,
            NonUnitalStarAlgHom.comp_id]
      _ = 0 := by rw [hu, map_zero]
  obtain ⟨v, hv⟩ := IsExact.mem_range J hu'
  refine ⟨map f (NonUnitalStarAlgHom.id ℂ J) v, ?_⟩
  calc _ = map f (NonUnitalStarAlgHom.id ℂ B)
          (map (NonUnitalStarAlgHom.id ℂ A) J.starAlgHom v) := by
        rw [MinTensorProduct.map_map, MinTensorProduct.map_map, NonUnitalStarAlgHom.id_comp,
          NonUnitalStarAlgHom.id_comp, NonUnitalStarAlgHom.comp_id, NonUnitalStarAlgHom.comp_id]
    _ = u := by
        rw [hv, MinTensorProduct.map_map, hfg, NonUnitalStarAlgHom.id_comp, MinTensorProduct.map_id,
          NonUnitalStarAlgHom.coe_id, id_eq]

end CStarAlgebra

end TauCeti
