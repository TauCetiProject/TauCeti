/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import TauCeti.AlgebraicGeometry.GroupScheme.Kernel
public import TauCeti.CategoryTheory.Monoidal.Grp.Translation
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Rank

/-!
# The rank of a homomorphism of group schemes

Let `f : G ⟶ H` be a homomorphism of group schemes over a scheme `S` whose underlying morphism of
schemes is finite and flat, so that it has a rank `Scheme.Hom.finrank` at every point of `H`. This
file proves that the rank of `f` at every point of its image is the rank at the identity of the
fibre: for a point `x` of `G` over `s ∈ S`, the rank of `f` at `f x` is the rank of `f` at `e_H(s)`.
The latter is the rank at `s` of the kernel of `f`, the fibre of `f` over the identity section,
which is finite and flat over `S`. In particular, when `f` is surjective its rank is constant along
the fibres of `H ⟶ S`, and it is a function on the base `S`: this is how the degree of an isogeny
is defined.

The proof is a translation argument after base change to `G`. The base change
`f ▷ G : G ×_S G ⟶ H ×_S G` of `f` intertwines left translation by the tautological point on
`G ×_S G` with left translation by its image under `f` on `H ×_S G` (`leftTranslationProd`),
because `f` is a homomorphism. The latter carries the section `a ↦ (1, a)` of `H ×_S G` to the
section `a ↦ (f a, a)`. Translations are isomorphisms, so the base change of `f` has the same rank
at the images of these two sections at `x`, and those are the ranks of `f` at `e_H(s)` and at
`f x`.

## Main results

* `TauCeti.GroupScheme.finrank_left_apply`: the rank of `f` at `f x` is the rank of `f` at the
  identity of the fibre through `f x`.
* `TauCeti.GroupScheme.finrank_left_eq`: for surjective `f`, the rank of `f` at any point `y` of
  `H` is the rank at the identity of the fibre through `y`.
* `TauCeti.GroupScheme.finrank_kernel_hom`: the rank of the kernel of `f` over `S` at `s` is the
  rank of `f` at the identity of the fibre over `s`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.12 and 2.4.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

universe u

namespace TauCeti.GroupScheme

section Rank

variable {S : Scheme.{u}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H) [IsMonHom f]
  [IsFinite f.left] [Flat f.left]

/-- **The rank of a homomorphism of group schemes is translation invariant.** If `f : G ⟶ H` is a
homomorphism of group schemes over `S` whose underlying morphism is finite and flat, then for a
point `x` of `G` over `s ∈ S`, the rank of `f` at `f x` equals its rank at the identity `e_H(s)` of
the fibre of `H` over `s`. -/
theorem finrank_left_apply (x : G.left) :
    f.left.finrank (f.left x) = f.left.finrank (η[H].left (G.hom x)) := by
  -- `f ▷ G : G ⊗ G ⟶ H ⊗ G` is the base change of `f` along the first projection of `H ⊗ G`
  have hpb : IsPullback (fst G G).left (f ▷ G).left f.left (fst H G).left := by
    have : IsPullback (fst G G) (f ▷ G) f (fst H G) :=
      IsPullback.of_isLimit' ⟨by simp⟩ <|
        PullbackCone.IsLimit.mk _ (fun c ↦ lift c.fst (c.snd ≫ snd H G)) (fun c ↦ by simp)
          (fun c ↦ by ext <;> simp [← c.condition]) (fun c m h₁ h₂ ↦ by ext <;> simp [← h₁, ← h₂])
    exact this.map (Over.forget S)
  have : IsFinite (f ▷ G).left := MorphismProperty.of_isPullback hpb ‹_›
  have : Flat (f ▷ G).left := MorphismProperty.of_isPullback hpb ‹_›
  -- translation by the tautological point on `G ⊗ G`, and by its image on `H ⊗ G`
  let σG := leftTranslationProd (𝟙 G)
  let σH := leftTranslationProd f
  have hσ : σG.hom.left ≫ (f ▷ G).left = (f ▷ G).left ≫ σH.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, leftTranslationProd_hom_comp_whiskerRight,
      Category.id_comp]
  -- the base change of `f` has the same rank at a point and at its translate
  have hrank (p : (H ⊗ G).left) : (f ▷ G).left.finrank (σH.hom.left p) =
      (f ▷ G).left.finrank p := by
    have := Scheme.Hom.finrank_comp_right_of_isIso (f ▷ G).left σH.hom.left p
    rwa [← hσ, Scheme.Hom.finrank_comp_left_of_isIso] at this
  -- the sections `a ↦ (1, a)` of `H ⊗ G` and its translate `a ↦ (f a, a)`, evaluated at `x` and
  -- projected to `H`
  let e : G ⟶ H ⊗ G := lift 1 (𝟙 G)
  have he : (fst H G).left (e.left x) = η[H].left (G.hom x) := by
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left]
    simp [e, Hom.one_def]
  have hσe : (fst H G).left (σH.hom.left (e.left x)) = f.left x := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left,
      ← Category.assoc]
    simp [e, σH]
  -- by base change, these are the ranks of `f` at `f x` and at `e_H(s)`
  have h := hrank (e.left x)
  rwa [Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb, Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb,
    hσe, he] at h

/-- **The rank of a surjective homomorphism of group schemes is constant along fibres.** If
`f : G ⟶ H` is a surjective homomorphism of group schemes over `S` whose underlying morphism is
finite and flat, then its rank at a point `y` of `H` over `s ∈ S` is its rank at the identity of
the fibre of `H` over `s`. -/
theorem finrank_left_eq [Surjective f.left] (y : H.left) :
    f.left.finrank y = f.left.finrank (η[H].left (H.hom y)) := by
  obtain ⟨x, rfl⟩ := f.left.surjective y
  rw [finrank_left_apply, ← Scheme.Hom.comp_apply f.left H.hom, Over.w f]

end Rank

section Kernel

variable {S : Scheme.{u}} {G H : Grp (Over S)} (f : G ⟶ H)

/-- **The rank of the kernel.** If `f : G ⟶ H` is a homomorphism of group schemes over `S` whose
underlying morphism is finite and flat, the rank of its kernel over `S` at `s` is the rank of `f`
at the identity `e_H(s)`: the kernel is the fibre of `f` over the identity section. -/
theorem finrank_kernel_hom [IsFinite f.hom.hom.left] [Flat f.hom.hom.left] (s : S) :
    (kernel f).X.hom.finrank s = f.hom.hom.left.finrank (η[H.X].left s) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_kernel_left f) s

end Kernel

end TauCeti.GroupScheme
