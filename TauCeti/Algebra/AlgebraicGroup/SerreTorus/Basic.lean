/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SerreTorus.CharacterLattice
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.Equivalence
public import TauCeti.Algebra.AlgebraicGroup.Torus.CharacterLattice.EssentialImage

/-!
# The Serre torus of a CM field

For a CM field `L`, the **Serre torus** `S^L` is the `ℚ`-torus whose character lattice is the
Galois lattice `TauCeti.SerreTorus.characterLattice L` of characters `χ ∈ ℤ[Hom(L, ℚ^al)]` with
constant sums `χ(φ) + χ(φ ∘ c)` over conjugate pairs of embeddings. Since tori over `ℚ` are
classified by their character lattices, `S^L` is constructed as the torus with this character
lattice, which determines it up to isomorphism.

Morphisms of tori `S^L → T`, which are morphisms `O(T) → O(S^L)` of coordinate Hopf algebras,
correspond to equivariant maps `X^*(T) → X^*(S^L)`. Combined with the universal property of the
universal cocharacter on the lattice side this gives the universal property of `(S^L, μ^L)`: for
an embedding `ι₀ : L → ℚ^al` and a lift `τ ∈ Gal(ℚ^al/ℚ)` of complex conjugation, every
cocharacter `μ` of a `ℚ`-torus `T`, read as a functional on `X^*(T)`, which is defined over `ι₀(L)`
and satisfies `(σ - 1)(τ + 1) μ = 0` for all `σ`, is the image of `μ^L` under a unique morphism
`S^L → T`.

## Main definitions

* `TauCeti.SerreTorus.torus L`: the coordinate Hopf algebra of the Serre torus `S^L`.
* `TauCeti.SerreTorus.characterLatticeIso L`: its character lattice is `characterLattice L`.
* `TauCeti.SerreTorus.homEquiv L T`: morphisms `S^L → T` are equivariant maps
  `X^*(T) → X^*(S^L)`.

## Main results

* `TauCeti.SerreTorus.existsUnique_universalCocharacter_comp_homEquiv`: the universal property
  of `(S^L, μ^L)`.

## References

* J. S. Milne and K.-y. Shih, *Langlands's construction of the Taniyama group*, in *Hodge cycles,
  motives, and Shimura varieties*, Lecture Notes in Math. 900 (1982), §1, pp. 230–232.
-/

public section

open CategoryTheory NumberField

namespace TauCeti.SerreTorus

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

/-- **The Serre torus** `S^L` of a CM field `L`, as the coordinate Hopf algebra of the `ℚ`-torus
whose character lattice is `characterLattice L`. -/
noncomputable def torus : TorusCommHopfAlgCat ℚ :=
  TorusCommHopfAlgCat.characterLatticeFunctor.objPreimage (characterLattice L)

/-- The character lattice of the Serre torus is `characterLattice L`. -/
noncomputable def characterLatticeIso :
    TorusCommHopfAlgCat.characterLatticeFunctor.obj (torus L) ≅ characterLattice L :=
  TorusCommHopfAlgCat.characterLatticeFunctor.objObjPreimageIso (characterLattice L)

/-- Morphisms of tori `S^L → T`, that is morphisms `O(T) → O(S^L)` of coordinate Hopf algebras,
are the equivariant maps from the character lattice of `T` to that of `S^L`. -/
noncomputable def homEquiv (T : TorusCommHopfAlgCat ℚ) :
    (T ⟶ torus L) ≃
      (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj.ρ.IntertwiningMap
        (characterSubrep L).toRepresentation :=
  (Functor.FullyFaithful.ofFullyFaithful TorusCommHopfAlgCat.characterLatticeFunctor).homEquiv.trans
    <| ((Iso.refl _).homCongr (characterLatticeIso L)).trans
      <| (galoisLatticeProperty ℚ).fullyFaithfulι.homEquiv.trans Rep.homEquiv

/-- The equivariant map attached to a morphism `f : S^L → T` is the map `f^*` on character
lattices followed by the identification of the character lattice of `S^L`. -/
theorem homEquiv_apply (T : TorusCommHopfAlgCat ℚ) (f : T ⟶ torus L) :
    homEquiv L T f =
      (TorusCommHopfAlgCat.characterLatticeFunctor.map f ≫
        (characterLatticeIso L).hom).hom.hom := by
  simp only [homEquiv, Equiv.trans_apply, Functor.FullyFaithful.homEquiv_apply,
    Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
  -- What remains is the inclusion of the full subcategory followed by `Rep.homEquiv`, which are
  -- the projections `.hom` and `.hom` of a morphism by definition.
  rfl

variable {L}

/-- **The universal property of the Serre torus.** Let `ι₀ : L → ℚ^al` be an embedding and
`τ ∈ Gal(ℚ^al/ℚ)` a lift of complex conjugation along it. A cocharacter `μ` of a `ℚ`-torus `T`, read
as a functional on the character lattice of `T`, which is defined over `ι₀(L)` and satisfies the
Serre relation `(σ - 1)(τ + 1) μ = 0`, is the image of the universal cocharacter under a unique
morphism `S^L → T`. -/
theorem existsUnique_universalCocharacter_comp_homEquiv (T : TorusCommHopfAlgCat ℚ)
    {ι₀ : L →ₐ[ℚ] AlgebraicClosure ℚ} {τ : Field.absoluteGaloisGroup ℚ}
    (hτ : τ • ι₀ = conjEmbedding L ι₀)
    {μ : Module.Dual ℤ (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj}
    (hstab : ∀ σ, σ • ι₀ = ι₀ →
      (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj.ρ.dual σ μ = μ)
    (hrel : ∀ σ, (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj.ρ.dual σ
      (μ + (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj.ρ.dual τ μ) =
        μ + (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj.ρ.dual τ μ) :
    ∃! f : T ⟶ torus L, universalCocharacter L ι₀ ∘ₗ (homEquiv L T f).toLinearMap = μ := by
  rw [(homEquiv L T).existsUnique_congr_right
    (q := fun g ↦ universalCocharacter L ι₀ ∘ₗ g.toLinearMap = μ)]
  exact ExistsUnique.intro (lift _ ι₀ τ μ hτ hstab hrel)
    (universalCocharacter_comp_lift (TorusCommHopfAlgCat.characterLatticeFunctor.obj T).obj.ρ
      hτ hstab hrel)
    fun g hg ↦ eq_lift _ hτ hstab hrel g hg

end TauCeti.SerreTorus
