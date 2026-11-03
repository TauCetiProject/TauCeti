/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RepresentationTheory.Rep.Res

/-!
# Internal homs under change of group

For a group homomorphism `f : G →* H`, an equivariant map `φ : A ⟶ Rep.res f B`,
and a module `N` with trivial action, precomposition with `φ` gives an equivariant map
`Res(f)(Homₖ(B, N)) ⟶ Homₖ(A, N)`.
This is the coefficient map on dual representations used in contravariant change of group
for cohomology. Its underlying linear map sends `ℓ` to `ℓ ∘ φ`.
-/

public section

noncomputable section

open CategoryTheory Rep

namespace MonoidHom

universe u v w t

variable {k : Type u} [CommRing k] {G : Type v} {H : Type w} [Group G] [Group H]
  (f : G →* H) {A : Rep.{t} k G} {B : Rep.{t} k H}
  (N : Type t) [AddCommGroup N] [Module k N]

/-- Precomposition with an equivariant map along `f`, as a morphism between the internal hom
representations. -/
def ihomTrivialPrecomp (φ : A ⟶ res f B) :
    res f ((Rep.ihom B).obj (Rep.trivial k H N)) ⟶
      (Rep.ihom A).obj (Rep.trivial k G N) :=
  Rep.ofHom ⟨LinearMap.lcomp k N φ.hom.toLinearMap, fun g ↦ by
    ext (ℓ : B →ₗ[k] N) a
    -- The internal homs are stored as bundled representations; expose their linear-map
    -- carriers to express the intertwining identity pointwise.
    change ℓ (B.ρ (f g)⁻¹ (φ.hom a)) = ℓ (φ.hom (A.ρ g⁻¹ a))
    simpa using congrArg ℓ (Rep.hom_comm_apply φ g⁻¹ a).symm⟩

/-- The internal-hom map along `f` acts by precomposition. -/
-- Match before simplification changes the presentation of the internal-hom carrier.
@[simp↓]
theorem ihomTrivialPrecomp_hom_apply (φ : A ⟶ res f B) (ℓ : B →ₗ[k] N) (a : A) :
    DFunLike.coe (F := A →ₗ[k] N) ((f.ihomTrivialPrecomp N φ).hom ℓ) a = ℓ (φ.hom a) :=
  (rfl)

/-- The identity on a representation induces the identity on its internal hom into a trivial
representation. -/
@[simp]
theorem ihomTrivialPrecomp_id (A : Rep.{t} k G) :
    (MonoidHom.id G).ihomTrivialPrecomp N (𝟙 A) =
      𝟙 ((Rep.ihom A).obj (Rep.trivial k G N)) :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

/-- Change of group and precomposition reverse composites of compatible coefficient maps. -/
@[reassoc]
theorem ihomTrivialPrecomp_comp {K : Type*} [Group K] (g : H →* K)
    {C : Rep.{t} k K} (φ : A ⟶ res f B) (ψ : B ⟶ res g C) :
    (g.comp f).ihomTrivialPrecomp N (φ ≫ (resFunctor f).map ψ) =
      (resFunctor f).map (g.ihomTrivialPrecomp N ψ) ≫ f.ihomTrivialPrecomp N φ :=
  Rep.hom_ext <| Representation.IntertwiningMap.ext <|
    LinearMap.ext fun _ ↦ LinearMap.ext fun _ ↦ rfl

end MonoidHom
