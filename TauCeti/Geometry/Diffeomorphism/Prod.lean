/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group

/-!
# Products of diffeomorphism groups

The geometric-topology roadmap builds relative diffeomorphism groups such as `Diff(M, ∂M)` as
pointwise-fixing subgroups of the self-diffeomorphism group. Product-region constructions there
need the corresponding product action on a product manifold. This file records the elementary
product homomorphism for that algebraic layer: a pair of self-diffeomorphisms acts on a product
manifold by the product diffeomorphism `Diffeomorph.prodCongr`.

This is a small prerequisite for the layer-3 relative group setup in
`TauCetiRoadmap/GeometricTopology/README.md`, "diffeomorphism groups with the C^∞ topology".
It is purely algebraic: the future `C^∞` topology and topological-group statements are not used
here. The relative restriction to pointwise-fixing subgroups is in
`TauCeti.Geometry.Diffeomorphism.RelativeProd`.

## Main definitions

* `TauCeti.Diffeomorph.prodHom`: the homomorphism
  `Diff(M) × Diff(N) → Diff(M × N)` given by `Diffeomorph.prodCongr`.

## Main results

* `TauCeti.Diffeomorph.prodHom_apply_apply`: the product homomorphism acts by
  `(φ, ψ) ↦ fun (x, y) => (φ x, ψ y)`.
* `TauCeti.Diffeomorph.prodHom_injective`: if both factors are nonempty, a product
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

end Diffeomorph

end TauCeti
