/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.CenterMap
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.CentralCharacter
public import TauCeti.RingTheory.Idempotents.Corner.Line
public import TauCeti.RingTheory.Idempotents.Primitive.AlgHom

/-!
# Blocks with a central character stay blocks under scalar extension

Let `k ⊆ k'` be fields, `G` a finite group and `e_B` a block idempotent of `k[G]` with a central
character, a `k`-algebra homomorphism `λ_B : Z(k[G]) → k` with `λ_B(e_B) = 1`. Then the image of
`e_B` in `k'[G]` is again a block idempotent.

The local ring `Z(k[G]) e_B` is Artinian with residue field `k` through `λ_B`, so its maximal
ideal consists of nilpotent elements, and the class sums span both centres; primitivity then
survives the map (`TauCeti.IsPrimitiveIdempotent.map_of_span_eq_top`).

Every block has a central character when `k` is algebraically closed, so then the blocks of `k[G]`
stay blocks of `k'[G]`. The same holds when `k` only splits `G`, once central characters are known
to exist over a splitting field; neither splitting fields nor that existence are formalized here.
A block has a central character whenever every class sum acts on it by a scalar,
`e_B K_C ∈ k e_B`, that is when `Z(k[G]) e_B` is the line `k e_B`; this condition survives every
field homomorphism `k → k'`, so such a block stays a block along every tower of extensions.

Without the central character this fails: along `𝔽₂ ⊆ 𝔽₄` the block `r + r²` of `𝔽₂[C₃]`, which
has none, splits into two blocks of `𝔽₄[C₃]`
(`TauCeti.GroupAlgebraBlockExamples.not_isBlockIdempotent_centerMapRingHom_r_add_r_sq`).

## Main results

* `TauCeti.IsBlockIdempotent.centerMapRingHom`: a block idempotent of `k[G]`
  with a central character maps to a block idempotent of `k'[G]` along every field homomorphism
  `k → k'`; `TauCeti.IsBlockIdempotent.centerMapRingHom_of_isAlgClosed` for
  `k` algebraically closed, where every block has a central character.
* `TauCeti.IsBlockIdempotent.exists_algHom_of_forall_exists_mul_classSumCenter`: a block on which
  every class sum acts by a scalar has a central character.
* `TauCeti.IsBlockIdempotent.centerMapRingHom_of_forall_exists_mul_classSumCenter`: such a block
  stays a block along every `k → k'`, and its image again has class sums acting by scalars
  (`TauCeti.exists_mul_classSumCenter_centerMapRingHom`).
-/

public section

namespace TauCeti

open _root_.MonoidAlgebra

variable {k k' G : Type*} [Field k] [Field k'] [Group G] [Finite G]

/-- **Blocks with a central character stay blocks.** Let `f : k →+* k'` be a homomorphism of
fields, `G` a finite group, and `e_B` a block idempotent of `k[G]` with a central character
`φ : Z(k[G]) → k`, `φ(e_B) = 1`. Then the image of `e_B` in `k'[G]` is a block idempotent. -/
theorem IsBlockIdempotent.centerMapRingHom (f : k →+* k')
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k} (hφ : φ b = 1) :
    IsBlockIdempotent (centerMapRingHom G f b) := by
  classical
  have := Fintype.ofFinite G
  refine IsPrimitiveIdempotent.map_of_span_eq_top hb hφ f
    (MonoidAlgebra.centerMapRingHom G f) (centerMapRingHom_algebraMap G f) ?_ fun h => hb.ne_zero ?_
  · -- The class sums of `k'[G]` span its centre, and they are images of class sums.
    rw [eq_top_iff, ← (classSumBasis (k := k') (G := G)).span_eq, Submodule.span_le]
    rintro _ ⟨C, rfl⟩
    exact Submodule.subset_span
      ⟨classSumCenter C, by rw [classSumBasis_apply, centerMapRingHom_classSumCenter]⟩
  · exact Subtype.ext <| mapRingHom_injective f.injective <| by
      simpa using congrArg Subtype.val h

/-- **Blocks over an algebraically closed field stay blocks.** For `k` algebraically closed and
`f : k →+* k'` a homomorphism of fields, the image of a block idempotent of `k[G]` in `k'[G]` is a
block idempotent: its central character exists. -/
theorem IsBlockIdempotent.centerMapRingHom_of_isAlgClosed [IsAlgClosed k]
    (f : k →+* k') {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) :
    IsBlockIdempotent (MonoidAlgebra.centerMapRingHom G f b) :=
  hb.centerMapRingHom f hb.centralCharacter_self

section ClassSum

variable [Fintype G] [DecidableEq G]

omit [Finite G] in
/-- **A block on which the class sums act by scalars has a central character.** If
`e_B K_C ∈ k e_B` for every conjugacy class `C`, then `Z(k[G]) e_B = k e_B`, and `z ↦ φ(z)` with
`e_B z = φ(z) e_B` is a central character of `B`. -/
theorem IsBlockIdempotent.exists_algHom_of_forall_exists_mul_classSumCenter
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (h : ∀ C : ConjClasses G, ∃ c : k, b * classSumCenter C = c • b) :
    ∃ φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k, φ b = 1 ∧ ∀ z, b * z = φ z • b := by
  refine hb.isIdempotentElem.exists_algHom_of_forall_exists_mul_eq_smul hb.ne_zero
    (forall_exists_mul_eq_smul_of_span_eq_top (s := Set.range classSumCenter) ?_ ?_)
  · rw [← (classSumBasis (k := k) (G := G)).span_eq]
    exact congrArg (fun f ↦ Submodule.span k (Set.range f))
      (funext fun C ↦ (classSumBasis_apply C).symm)
  · rintro _ ⟨C, rfl⟩
    exact h C

/-- **Blocks on which the class sums act by scalars stay blocks.** If `e_B` is a block idempotent
of `k[G]` and `e_B K_C ∈ k e_B` for every class `C`, then the image of `e_B` in `k'[G]` is a block
idempotent for every field homomorphism `f : k →+* k'`, and it again satisfies the hypothesis
(`TauCeti.exists_mul_classSumCenter_centerMapRingHom`), so it stays a block along any further
extension. -/
theorem IsBlockIdempotent.centerMapRingHom_of_forall_exists_mul_classSumCenter (f : k →+* k')
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b)
    (h : ∀ C : ConjClasses G, ∃ c : k, b * classSumCenter C = c • b) :
    IsBlockIdempotent (MonoidAlgebra.centerMapRingHom G f b) := by
  obtain ⟨φ, hφ, -⟩ := hb.exists_algHom_of_forall_exists_mul_classSumCenter h
  exact hb.centerMapRingHom f hφ

end ClassSum

end TauCeti
