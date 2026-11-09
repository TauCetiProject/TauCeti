/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TensorProduct.MulSemiringAction
public import TauCeti.RingTheory.Etale.Torsor.Basic

/-!
# The tensor product of finite étale torsors

If `B` is a finite étale `G`-torsor and `C` a finite étale `H`-torsor over `A`, then `B ⊗[A] C`
is a finite étale `(G × H)`-torsor over `A`, with `G × H` acting factorwise
(`Algebra.TensorProduct.prodMulSemiringAction`). Geometrically, the fibre product over `Spec A`
of a `G`-torsor and an `H`-torsor is a `(G × H)`-torsor.

Iterating this gives the torsors `B₁ ⊗[A] ⋯ ⊗[A] Bₙ` under `G₁ × ⋯ × Gₙ`, as used for the levels of
the tower of finite étale torsors splitting every finite étale `A`-algebra.

## Main results

* `TauCeti.Algebra.IsFiniteEtaleTorsor.tensor`: `B ⊗[A] C` is a `(G × H)`-torsor over `A`.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, Theorem 1.3.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 15.3.
-/

public section

open TensorProduct

namespace TauCeti.Algebra

namespace IsFiniteEtaleTorsor

variable {G H A B C : Type*} [Group G] [Group H] [Finite G] [Finite H] [CommRing A] [CommRing B]
  [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] [CommRing C] [Algebra A C]
  [MulSemiringAction H C] [SMulCommClass H A C]

attribute [local instance] Algebra.TensorProduct.prodMulSemiringAction in
/-- **Tensor product of torsors.** If `B` is a finite étale `G`-torsor and `C` a finite étale
`H`-torsor over `A`, then `B ⊗[A] C` is a finite étale `(G × H)`-torsor over `A`, with `G × H`
acting factorwise (`Algebra.TensorProduct.prodMulSemiringAction`). Geometrically, the fibre
product of a `G`-torsor and an `H`-torsor over `Spec A` is a `(G × H)`-torsor. -/
instance tensor [hB : IsFiniteEtaleTorsor G A B] [hC : IsFiniteEtaleTorsor H A C] :
    IsFiniteEtaleTorsor (G × H) A (B ⊗[A] C) := by
  obtain ⟨_, _, hGB⟩ := isFiniteEtaleTorsor_iff.mp hB
  obtain ⟨_, _, hHC⟩ := isFiniteEtaleTorsor_iff.mp hC
  have := hB.faithfullyFlat
  have := hC.faithfullyFlat
  have : Module.FaithfullyFlat A (B ⊗[A] C) := .trans A B (B ⊗[A] C)
  -- Check the Chase–Harrison–Rosenberg criterion: invariants and freeness.
  refine isFiniteEtaleTorsor_iff.mpr ⟨inferInstance, ⟨fun z hz ↦ ?_⟩, fun k hk ↦ ?_⟩
  · -- Fixed by `1 × H`, the element `z` comes from `B`, since `B ⊗[A] C` is an `H`-torsor over
    -- `B` by base change; fixed by `G × 1`, that element of `B` comes from `A`.
    have hright (h : H) (w : B ⊗[A] C) : ((1 : G), h) • w =
        Algebra.TensorProduct.map (AlgHom.id B B) (MulSemiringAction.toAlgHom A C h) w := by
      induction w using TensorProduct.inductionOn with
      | tmul b c => simp
      | add x y hx hy => rw [smul_add, map_add, hx, hy]
    obtain ⟨b, rfl⟩ : ∃ b : B, algebraMap B (B ⊗[A] C) b = z := by
      let := Algebra.TensorProduct.rightMulSemiringAction (K := A) B C H
      refine Algebra.IsInvariant.isInvariant (A := B) (G := H) z fun h ↦ ?_
      rw [Algebra.TensorProduct.rightMulSemiringAction_smul_def, ← hright, hz]
    have hinj := FaithfulSMul.algebraMap_injective B (B ⊗[A] C)
    obtain ⟨a, rfl⟩ := Algebra.IsInvariant.isInvariant (A := A) (G := G) b fun g ↦ hinj <| by
      simpa using hz (g, 1)
    exact ⟨a, (IsScalarTower.algebraMap_apply A B (B ⊗[A] C) a).symm⟩
  · -- A nonidentity `(g, h)` has `g ≠ 1` or `h ≠ 1`, and the differences `g • b - b` on `B`, or
    -- `h • c - c` on `C`, push forward to differences `(g, h) • z - z` on `B ⊗[A] C`.
    rw [← top_le_iff]
    by_cases hg : k.1 = 1
    · have hh : k.2 ≠ 1 := fun hh ↦ hk (Prod.ext hg hh)
      rw [← Ideal.map_top (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C), ← hHC k.2 hh,
        Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨1 ⊗ₜ c, by simp [hg, tmul_sub]⟩
    · rw [← Ideal.map_top (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] C), ← hGB k.1 hg,
        Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨b ⊗ₜ 1, by simp [sub_tmul]⟩

end IsFiniteEtaleTorsor

end TauCeti.Algebra
