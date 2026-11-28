/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Graph

/-!
# Goursat's dichotomy for two Lie algebras

A Lie subalgebra projecting onto both factors of a product is the whole product or the
graph of a surjective Lie homomorphism when the second factor has only trivial ideals.
If both factors have only trivial ideals, the homomorphism in the graph case is a Lie
equivalence. The asymmetric version also applies when the first factor is itself a product.

This is the two-factor Lie algebra argument used in Lawrence and Venkatesh,
*Diophantine problems and p-adic period mappings*, §2.7, preceding Lemma 2.12.
-/

public section

namespace LieSubalgebra

variable {R L₁ L₂ : Type*} [CommRing R] [LieRing L₁] [LieAlgebra R L₁]
  [LieRing L₂] [LieAlgebra R L₂]

/-- If the second factor has only trivial ideals, a Lie subalgebra projecting onto both
factors is the full product or the graph of a surjective Lie homomorphism. -/
theorem eq_top_or_exists_surjective_lieHom_graph (S : LieSubalgebra R (L₁ × L₂))
    (h₂ : ∀ I : LieIdeal R L₂, I = ⊥ ∨ I = ⊤)
    (p₁ : Function.Surjective (fun x : S => x.val.1))
    (p₂ : Function.Surjective (fun x : S => x.val.2)) :
    S = ⊤ ∨ ∃ f : L₁ →ₗ⁅R⁆ L₂, Function.Surjective f ∧ S = f.graph := by
  let fst := (LieHom.fst R L₁ L₂).comp S.incl
  let snd := (LieHom.snd R L₁ L₂).comp S.incl
  rcases h₂ (fst.ker.map snd) with hzero | hfull
  · have hinj : Function.Injective fst := by
      apply fst.ker_eq_bot.mp
      apply _root_.eq_bot_iff.mpr
      intro x hx
      exact (LieSubmodule.mem_bot _).2 (Subtype.ext (Prod.ext (fst.mem_ker.mp hx)
        (snd.mem_ker.mp (LieIdeal.map_eq_bot_iff.mp hzero hx))))
    let e := LieEquiv.ofBijective fst ⟨hinj, p₁⟩
    let f := snd.comp e.symm.toLieHom
    have hcoord (x : S) : f x.val.1 = x.val.2 := congrArg snd (e.symm_apply_apply x)
    refine Or.inr ⟨f, p₂.comp e.symm.surjective, ?_⟩
    ext p
    rw [LieHom.mem_graph_iff]
    constructor
    · intro hp
      exact (hcoord ⟨p, hp⟩).symm
    · intro hp
      obtain ⟨x, hx⟩ := p₁ p.1
      have heq : x.val = p := Prod.ext hx <| calc
        x.val.2 = f x.val.1 := (hcoord x).symm
        _ = f p.1 := congrArg f hx
        _ = p.2 := hp.symm
      exact heq ▸ x.property
  · left
    apply eq_top_iff.mpr
    rintro ⟨a, b⟩ _
    obtain ⟨x, hx⟩ := p₁ a
    have hmem : b - snd x ∈ fst.ker.map snd := hfull ▸ LieSubmodule.mem_top _
    obtain ⟨y, hy⟩ := LieIdeal.mem_map_of_surjective p₂ hmem
    have hfst : fst (x + y.val) = a := by
      rw [map_add, fst.mem_ker.mp y.property, add_zero]
      exact hx
    have hsnd : snd (x + y.val) = b := by rw [map_add, hy, add_sub_cancel]
    exact (Prod.ext hfst hsnd : (x + y.val).val = (a, b)) ▸ (x + y.val).property

/-- **Two-factor Goursat dichotomy**. If each factor has only trivial Lie ideals, every
Lie subalgebra surjecting onto both factors is the full product or the graph of a Lie
equivalence. In particular this applies to two nonabelian simple Lie algebras over a field. -/
theorem eq_top_or_exists_lieEquiv_graph (S : LieSubalgebra R (L₁ × L₂))
    (h₁ : ∀ I : LieIdeal R L₁, I = ⊥ ∨ I = ⊤)
    (h₂ : ∀ I : LieIdeal R L₂, I = ⊥ ∨ I = ⊤)
    (p₁ : Function.Surjective (fun x : S => x.val.1))
    (p₂ : Function.Surjective (fun x : S => x.val.2)) :
    S = ⊤ ∨ ∃ e : L₁ ≃ₗ⁅R⁆ L₂, S = e.toLieHom.graph := by
  obtain h | ⟨f, hf, hS⟩ := S.eq_top_or_exists_surjective_lieHom_graph h₂ p₁ p₂
  · exact Or.inl h
  rcases h₁ f.ker with hker | hker
  · exact Or.inr ⟨LieEquiv.ofBijective f ⟨f.ker_eq_bot.mp hker, hf⟩, hS⟩
  · have hzero (b : L₂) : b = 0 := by
      obtain ⟨a, rfl⟩ := hf b
      exact f.mem_ker.mp (hker ▸ LieSubmodule.mem_top a)
    left
    rw [hS, eq_top_iff]
    exact fun x _ => (f.mem_graph_iff x).2 ((hzero x.2).trans (hzero _).symm)

end LieSubalgebra
