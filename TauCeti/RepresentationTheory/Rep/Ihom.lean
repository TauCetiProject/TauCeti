/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# Internal homs of representations: exactness and change of group

The internal hom `Rep.ihom A`, sending a representation `B` to `Homₖ(A, B)`, is an additive
functor. When the underlying module of `A` is projective over `k`, it is exact: it takes a short
exact sequence of representations to a short exact sequence (`Rep.shortExact_map_ihom`), since
exactness of representations is tested on underlying modules and `Homₖ(A, -)` is exact on
`k`-modules for projective `A`. Applied to trivial representations, this gives the short exact
sequences of coefficients `Homₖ(A, N)` along which group cohomology with coefficients in an
internal hom has its long exact sequence.

For a group homomorphism `f : G →* H`, an equivariant map `φ : A ⟶ Rep.res f B`,
and a module `N` with trivial action, precomposition with `φ` gives an equivariant map
`Res(f)(Homₖ(B, N)) ⟶ Homₖ(A, N)`.
This is the coefficient map on dual representations used in contravariant change of group
for cohomology. Its underlying linear map sends `ℓ` to `ℓ ∘ φ`.
-/

public section

noncomputable section

open CategoryTheory Rep

namespace Rep

universe u v w

variable {k : Type u} [CommRing k] {G : Type v} [Group G] (A : Rep.{w} k G)

/-- The internal hom out of a representation is an additive functor. -/
instance : (Rep.ihom A).Additive where
  map_add := rfl

/-- **The internal hom out of a `k`-projective representation is exact**: if the underlying module
of `A` is projective over `k`, then `Homₖ(A, -)` takes a short exact sequence of representations
`0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` to the short exact sequence
`0 ⟶ Homₖ(A, X₁) ⟶ Homₖ(A, X₂) ⟶ Homₖ(A, X₃) ⟶ 0`. -/
theorem shortExact_map_ihom [Module.Projective k A] {S : ShortComplex (Rep.{w} k G)}
    (hS : S.ShortExact) : (S.map (Rep.ihom A)).ShortExact := by
  have hfg := (exact_iff_function_exact S).1 hS.exact
  have hf := (mono_iff_injective S.f).1 hS.mono_f
  have hg := (epi_iff_surjective S.g).1 hS.epi_g
  -- The maps of the image sequence are postcomposition with the maps of `S`, on `k`-linear maps
  -- out of `A`.
  refine
    { exact := (exact_iff_function_exact _).2 fun (ℓ : A →ₗ[k] S.X₂) ↦ ⟨fun h ↦ ?_, ?_⟩
      mono_f := (mono_iff_injective _).2 fun (ℓ : A →ₗ[k] S.X₁) ℓ' h ↦
        LinearMap.ext fun a ↦ hf (LinearMap.congr_fun h a)
      epi_g := (epi_iff_surjective _).2 fun (ℓ : A →ₗ[k] S.X₃) ↦
        Module.projective_lifting_property S.g.hom.toLinearMap ℓ hg }
  · -- A map killed by `S.g` takes values in the range of `S.f`, through which it factors.
    have hℓ : ∀ a, ℓ a ∈ LinearMap.range S.f.hom.toLinearMap := fun a ↦ by
      rw [← LinearMap.exact_iff.1 hfg]
      exact LinearMap.congr_fun h a
    exact ⟨(LinearEquiv.ofInjective _ hf).symm.toLinearMap ∘ₗ ℓ.codRestrict _ hℓ,
      LinearMap.ext fun a ↦
        congrArg Subtype.val ((LinearEquiv.ofInjective _ hf).apply_symm_apply _)⟩
  · rintro ⟨(ℓ : A →ₗ[k] S.X₁), rfl⟩
    exact LinearMap.ext fun a ↦ hfg.apply_apply_eq_zero (ℓ a)

end Rep

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
