/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.FixingSubgroup

/-!
# Products of diffeomorphism groups

The geometric-topology roadmap builds relative diffeomorphism groups such as `Diff(M, ∂M)` as
pointwise-fixing subgroups of the self-diffeomorphism group. This file records the elementary
product API for that algebraic layer: a pair of self-diffeomorphisms acts on a product manifold by
the product diffeomorphism, and if the two factors fix subsets `s` and `t`, then the product fixes
the product subset `s ×ˢ t` pointwise.

This is a small prerequisite for the layer-3 relative group setup in
`TauCetiRoadmap/GeometricTopology/README.md`, "diffeomorphism groups with the C^∞ topology".
It is purely algebraic: the future `C^∞` topology and topological-group statements are not used
here.

## Main definitions

* `TauCeti.Diffeomorph.prodHom`: the homomorphism
  `Diff(M) × Diff(N) → Diff(M × N)` given by `Diffeomorph.prodCongr`.
* `TauCeti.Diffeomorph.relativeProdHom`: the restriction
  `Diff(M, s) × Diff(N, t) → Diff(M × N, s × t)`.

## Main results

* `TauCeti.Diffeomorph.prodHom_apply_apply`: the product homomorphism acts by
  `(φ, ψ) ↦ fun (x, y) => (φ x, ψ y)`.
* `TauCeti.Diffeomorph.prodCongr_mem_fixingSubgroup_prod`: product diffeomorphisms fix the
  product of two fixed subsets.
* `TauCeti.Diffeomorph.prodHom_injective` and
  `TauCeti.Diffeomorph.relativeProdHom_injective`: if both factors are nonempty, a product
  diffeomorphism determines its two factors.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω}

/-- The product homomorphism from pairs of self-diffeomorphisms to self-diffeomorphisms of the
product manifold. It sends `(φ, ψ)` to `φ.prodCongr ψ`. -/
@[expose]
def prodHom :
    (M ≃ₘ^n⟮I, I⟯ M) × (N ≃ₘ^n⟮J, J⟯ N) →*
      (M × N) ≃ₘ^n⟮I.prod J, I.prod J⟯ M × N where
  toFun p := p.1.prodCongr p.2
  map_one' := by
    ext x <;> rfl
  map_mul' p q := by
    ext x <;> rfl

/-- The product homomorphism is given by `Diffeomorph.prodCongr`. -/
theorem prodHom_apply (p : (M ≃ₘ^n⟮I, I⟯ M) × (N ≃ₘ^n⟮J, J⟯ N)) :
    prodHom (I := I) (J := J) (n := n) p = p.1.prodCongr p.2 :=
  rfl

/-- Pointwise formula for the product homomorphism. -/
@[simp, grind =]
theorem prodHom_apply_apply
    (p : (M ≃ₘ^n⟮I, I⟯ M) × (N ≃ₘ^n⟮J, J⟯ N)) (x : M × N) :
    prodHom (I := I) (J := J) (n := n) p x = (p.1 x.1, p.2 x.2) :=
  rfl

/-- If both factors are nonempty, the product homomorphism remembers both component
diffeomorphisms. The nonemptiness hypotheses are necessary: if one factor is empty, maps on the
product cannot see the other factor. -/
theorem prodHom_injective [Nonempty M] [Nonempty N] :
    Function.Injective
      (prodHom (I := I) (J := J) (n := n) :
        (M ≃ₘ^n⟮I, I⟯ M) × (N ≃ₘ^n⟮J, J⟯ N) →*
          (M × N) ≃ₘ^n⟮I.prod J, I.prod J⟯ M × N) := by
  rintro ⟨φ, ψ⟩ ⟨φ', ψ'⟩ h
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨y₀⟩ := (inferInstance : Nonempty N)
  apply Prod.ext
  · apply _root_.Diffeomorph.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun h (x, y₀))
  · apply _root_.Diffeomorph.ext
    intro y
    exact congrArg Prod.snd (DFunLike.congr_fun h (x₀, y))

/-- A product diffeomorphism fixes the product of two subsets pointwise when each factor fixes the
corresponding subset pointwise. -/
theorem prodCongr_mem_fixingSubgroup_prod {s : Set M} {t : Set N}
    {φ : M ≃ₘ^n⟮I, I⟯ M} {ψ : N ≃ₘ^n⟮J, J⟯ N}
    (hφ : φ ∈ fixingSubgroup (I := I) (n := n) s)
    (hψ : ψ ∈ fixingSubgroup (I := J) (n := n) t) :
    φ.prodCongr ψ ∈ fixingSubgroup (I := I.prod J) (n := n) (s ×ˢ t) := by
  rw [mem_fixingSubgroup_iff]
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact Prod.ext (apply_eq_of_mem_fixingSubgroup hφ hx) (apply_eq_of_mem_fixingSubgroup hψ hy)

/-- The product homomorphism restricted to relative diffeomorphism groups. A pair of
diffeomorphisms fixing `s` and `t` pointwise acts on the product and fixes `s ×ˢ t`
pointwise. -/
@[expose]
def relativeProdHom (s : Set M) (t : Set N) :
    fixingSubgroup (I := I) (n := n) s × fixingSubgroup (I := J) (n := n) t →*
      fixingSubgroup (I := I.prod J) (n := n) (s ×ˢ t) where
  toFun p :=
    ⟨(p.1 : M ≃ₘ^n⟮I, I⟯ M).prodCongr (p.2 : N ≃ₘ^n⟮J, J⟯ N),
      prodCongr_mem_fixingSubgroup_prod p.1.property p.2.property⟩
  map_one' := by
    ext x <;> rfl
  map_mul' p q := by
    ext x <;> rfl

/-- Applying `relativeProdHom` and forgetting the subgroup gives the product diffeomorphism. -/
@[simp]
theorem relativeProdHom_apply (s : Set M) (t : Set N)
    (p : fixingSubgroup (I := I) (n := n) s × fixingSubgroup (I := J) (n := n) t) :
    (relativeProdHom (I := I) (J := J) (n := n) s t p :
      (M × N) ≃ₘ^n⟮I.prod J, I.prod J⟯ M × N) =
      (p.1 : M ≃ₘ^n⟮I, I⟯ M).prodCongr (p.2 : N ≃ₘ^n⟮J, J⟯ N) :=
  rfl

/-- Pointwise formula for `relativeProdHom`. -/
@[simp, grind =]
theorem relativeProdHom_apply_apply (s : Set M) (t : Set N)
    (p : fixingSubgroup (I := I) (n := n) s × fixingSubgroup (I := J) (n := n) t)
    (x : M × N) :
    (relativeProdHom (I := I) (J := J) (n := n) s t p :
      (M × N) ≃ₘ^n⟮I.prod J, I.prod J⟯ M × N) x =
      ((p.1 : M ≃ₘ^n⟮I, I⟯ M) x.1, (p.2 : N ≃ₘ^n⟮J, J⟯ N) x.2) :=
  rfl

/-- If both factors are nonempty, the relative product homomorphism remembers both relative
diffeomorphisms. -/
theorem relativeProdHom_injective [Nonempty M] [Nonempty N] (s : Set M) (t : Set N) :
    Function.Injective
      (relativeProdHom (I := I) (J := J) (n := n) s t :
        fixingSubgroup (I := I) (n := n) s × fixingSubgroup (I := J) (n := n) t →*
          fixingSubgroup (I := I.prod J) (n := n) (s ×ˢ t)) := by
  intro p q h
  have hprod :
      prodHom (I := I) (J := J) (n := n)
          ((p.1 : M ≃ₘ^n⟮I, I⟯ M), (p.2 : N ≃ₘ^n⟮J, J⟯ N)) =
        prodHom (I := I) (J := J) (n := n)
          ((q.1 : M ≃ₘ^n⟮I, I⟯ M), (q.2 : N ≃ₘ^n⟮J, J⟯ N)) := by
    simpa [relativeProdHom_apply, prodHom_apply] using congrArg Subtype.val h
  have hpq := prodHom_injective (I := I) (J := J) (n := n) hprod
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hpq
  · apply Subtype.ext
    exact congrArg Prod.snd hpq

end Diffeomorph

end TauCeti
