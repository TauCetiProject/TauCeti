/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Maps out of complexes bounded above, through a map that is invertible in low degrees

Let `j : T ⟶ I` be a map of `ℤ`-indexed cochain complexes in a preadditive category which is an
isomorphism in degrees `≤ n` and a monomorphism in degree `n + 1`. For a complex `M` vanishing in
degrees `> n`, composition with `j` induces a bijection on homotopy classes of maps

```text
Hom_K(M, T) ≃ Hom_K(M, I).
```

Cochains `M ⟶ I` of degree `d ≤ 0` lift through `j`, degree by degree through the
isomorphisms `jᵏ`, `k ≤ n`. A lift of a cocycle of degree `0` is a cocycle, by cancelling the
monomorphisms `jᵏ⁺¹`, `k ≤ n`; and a homotopy, a cochain of degree `-1`, lifts as well. No
exactness or boundedness below is needed.

This is used to compare a complex with a truncation of it at a high degree, for instance a bounded
truncation of an injective resolution of a bounded complex.

## Main results

* `CochainComplex.bijective_comp_quotient_map_of_isIso_of_mono`: the bijection on morphisms of the
  homotopy category.
-/

public section

namespace CochainComplex

open CategoryTheory CategoryTheory.Limits HomComplex

variable {C : Type*} [Category* C] [Preadditive C] {M T I : CochainComplex C ℤ} (j : T ⟶ I)
  (n : ℤ) (hiso : ∀ k ≤ n, IsIso (j.f k)) [M.IsStrictlyLE n]

include hiso in
/-- The lift through `j` of a cochain `M ⟶ I` of degree `d ≤ 0`: in degrees `p ≤ n` it is the
composite with the inverse of `jᵠ`, `q = p + d ≤ n`, and it vanishes above, where `M` is zero. -/
private noncomputable def liftCochain {d : ℤ} (hd : d ≤ 0) (α : Cochain M I d) : Cochain M T d :=
  Cochain.mk fun p q hpq ↦
    if hp : p ≤ n then
      haveI := hiso q (by lia)
      α.v p q hpq ≫ inv (j.f q)
    else 0

private theorem liftCochain_comp {d : ℤ} (hd : d ≤ 0) (α : Cochain M I d) :
    (liftCochain j n hiso hd α).comp (Cochain.ofHom j) (add_zero d) = α := by
  ext p q hpq
  by_cases hp : p ≤ n
  · have := hiso q (by lia)
    simp [liftCochain, hp]
  · exact (M.isZero_of_isStrictlyLE n p (by lia)).eq_of_src _ _

omit hiso in
/-- Composition with `j` is injective on cochains `M ⟶ T` of degree `d` when `j` is a
monomorphism in the degrees `≤ n + d` that can be reached from `M`. -/
private theorem comp_ofHom_injective {d : ℤ} (hmono : ∀ q ≤ n + d, Mono (j.f q))
    {α β : Cochain M T d}
    (h : α.comp (Cochain.ofHom j) (add_zero d) = β.comp (Cochain.ofHom j) (add_zero d)) :
    α = β := by
  ext p q hpq
  by_cases hp : p ≤ n
  · have := hmono q (by lia)
    rw [← cancel_mono (j.f q)]
    simpa using Cochain.congr_v h p q hpq
  · exact (M.isZero_of_isStrictlyLE n p (by lia)).eq_of_src _ _

include hiso in
/-- **Maps out of a complex vanishing above `n` through a map that is an isomorphism in degrees
`≤ n` and a monomorphism in degree `n + 1`**: composition with `j` is a bijection on homotopy
classes. -/
theorem bijective_comp_quotient_map_of_isIso_of_mono (hmono : Mono (j.f (n + 1))) :
    Function.Bijective fun g : (HomotopyCategory.quotient C (.up ℤ)).obj M ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj T ↦
      g ≫ (HomotopyCategory.quotient C (.up ℤ)).map j := by
  have hmono₀ (q : ℤ) (hq : q ≤ n + 0) : Mono (j.f q) := by
    have := hiso q (by lia)
    infer_instance
  have hmono₁ (q : ℤ) (hq : q ≤ n + 1) : Mono (j.f q) := by
    rcases (show q ≤ n ∨ q = n + 1 by lia) with hq | rfl
    · have := hiso q hq
      infer_instance
    · exact hmono
  refine ⟨fun g₁ g₂ hg ↦ ?_, fun g ↦ ?_⟩
  · obtain ⟨f₁, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g₁
    obtain ⟨f₂, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g₂
    simp only [← Functor.map_comp] at hg
    obtain ⟨z, hz⟩ := Cochain.equivHomotopy _ _ (HomotopyCategory.homotopyOfEq _ _ hg)
    apply HomotopyCategory.eq_of_homotopy
    refine (Cochain.equivHomotopy _ _).symm ⟨liftCochain j n hiso (by lia) z, ?_⟩
    apply comp_ofHom_injective j n hmono₀
    rw [Cochain.add_comp, ← δ_comp_ofHom, liftCochain_comp, ← Cochain.ofHom_comp,
      ← Cochain.ofHom_comp, hz]
  · obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
    let α := liftCochain j n hiso le_rfl (Cochain.ofHom f)
    have hα : δ 0 1 α = 0 := by
      apply comp_ofHom_injective j n hmono₁
      rw [← δ_comp_ofHom, liftCochain_comp, δ_ofHom, Cochain.zero_comp]
    refine ⟨(HomotopyCategory.quotient C (.up ℤ)).map (Cocycle.homOf (Cocycle.mk α 1 rfl hα)),
      ?_⟩
    dsimp only
    rw [← Functor.map_comp]
    congr 1
    apply Cochain.ofHom_injective
    rw [Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.mk_coe,
      liftCochain_comp]

end CochainComplex
