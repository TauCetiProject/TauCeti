/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.Product

/-!
# The unit of the Tate cup product

The class of `1` in degree-zero Tate cohomology of the trivial representation is the unit
for the cup product in every integer degree. The two unit laws use the right and left unitors
of the tensor product of representations. These identities normalize the cup product used in
Tate's theorem, including when the order of the finite group vanishes in the coefficient ring.

The construction follows the standard normalization of the cup product in Artin and Tate,
*Class Field Theory*, Preliminaries §2.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The degree-zero Tate class of `1` in the trivial representation. -/
def cupUnit : tateCohomology (𝟙_ (Rep k G)) 0 :=
  H0π _ ⟨1, fun _ ↦ rfl⟩

/-- The class of `1` is a right unit for the Tate cup product, after the right unitor identifies
`M ⊗ 𝟙` with `M`. -/
@[simp]
theorem cup_right_unit (M : Rep k G) (p : ℤ) (x : tateCohomology M p) :
    (tateCohomologyFunctor p).map (ρ_ M).hom
      (cupH0 M (𝟙_ (Rep k G)) p x cupUnit) = x := by
  rw [cupUnit, cupH0_H0π, ← ModuleCat.comp_apply, ← Functor.map_comp]
  have h : Rep.tensorInvariant M (⟨1, fun _ ↦ rfl⟩ : (𝟙_ (Rep k G)).ρ.invariants) ≫
      (ρ_ M).hom = 𝟙 M := by
    ext m
    have ht : (Rep.tensorInvariant M
        (⟨1, fun _ ↦ rfl⟩ : (𝟙_ (Rep k G)).ρ.invariants)).hom m = m ⊗ₜ[k] (1 : k) :=
      Rep.tensorInvariant_hom_apply M _ m
    simpa [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.comp_apply]
      using congrArg (TensorProduct.rid k M.V) ht
  simp [h]

/-- The class of `1` is a left unit for the Tate cup product, after the left unitor identifies
`𝟙 ⊗ M` with `M`. -/
@[simp]
theorem cup_left_unit (M : Rep k G) (p : ℤ) (x : tateCohomology M p) :
    (tateCohomologyFunctor p).map (λ_ M).hom
      (cup0H (𝟙_ (Rep k G)) M p cupUnit x) = x := by
  rw [cup0H_apply, ← ModuleCat.comp_apply, ← Functor.map_comp,
    braiding_leftUnitor]
  simpa only [cup_zero_right] using cup_right_unit M p x

end TauCeti.TateCohomology
