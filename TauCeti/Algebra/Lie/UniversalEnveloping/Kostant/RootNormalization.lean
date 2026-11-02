/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Form

/-!
# Root normalization and transport of Kostant integral forms

Changing the sign of a Chevalley root vector changes its divided powers by integral units,
so it does not change the Kostant integral form. Repeating or reordering the root and Cartan
families does not change it either. These facts allow a rational Lie equivalence with signed,
renumbered root images to restrict to an equivalence of the specified integral forms.

The containment theorem also allows nonunit integer root scalings. Unit scalings give equality;
a rational change of root normalization need not preserve the integral form. No commutativity,
root relations or independence of the supplied families is needed for these statements.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
variable {ι κ ι' κ' : Type*}

attribute [local instance] TauCeti.moduleNNRat

/-- Replacing each root vector by an integer multiple of a designated root vector, and using
only designated Cartan vectors, gives a subring of the original Kostant form. -/
theorem kostantForm_le_of_root_zsmul (e : ι → L) (h : κ → L)
    (e' : ι' → L) (h' : κ' → L)
    (he : ∀ i, ∃ j, ∃ z : ℤ, e' i = z • e j)
    (hh : Set.range h' ⊆ Set.range h) :
    kostantForm e' h' ≤ kostantForm e h := by
  refine (kostantForm_le_iff _ _ _).mpr ⟨?_, ?_⟩
  · intro i n
    obtain ⟨j, z, hz⟩ := he i
    rw [hz, map_zsmul, Associative.dividedPower_zsmul]
    exact Subring.zsmul_mem _ (dividedPower_mem_kostantForm e h j n) _
  · intro i n
    obtain ⟨j, hj⟩ := hh ⟨i, rfl⟩
    rw [← hj]
    exact ringChoose_mem_kostantForm e h j n

/-- Independent integral unit scalings of the root vectors preserve the Kostant form.
Over `ℤ`, these units are exactly the choices of root-vector signs. -/
@[simp]
theorem kostantForm_root_units (e : ι → L) (h : κ → L) (u : ι → ℤˣ) :
    kostantForm (fun i => (u i : ℤ) • e i) h = kostantForm e h := by
  apply le_antisymm
  · exact kostantForm_le_of_root_zsmul e h _ h
      (fun i => ⟨i, u i, rfl⟩) (Set.Subset.refl _)
  · refine kostantForm_le_of_root_zsmul _ h e h ?_ (Set.Subset.refl _)
    intro i
    refine ⟨i, ↑(u i)⁻¹, ?_⟩
    simp [smul_smul]

/-- Surjective reindexing of either generating family preserves the Kostant form.
In particular, ordering and repeated generators have no effect. -/
theorem kostantForm_reindex (e : ι → L) (h : κ → L)
    (σ : ι' → ι) (τ : κ' → κ) (hσ : Function.Surjective σ)
    (hτ : Function.Surjective τ) :
    kostantForm (e ∘ σ) (h ∘ τ) = kostantForm e h := by
  apply le_antisymm
  · exact kostantForm_le_of_root_zsmul e h _ _
      (fun i => ⟨σ i, 1, by simp⟩) (by rintro _ ⟨i, rfl⟩; exact ⟨τ i, rfl⟩)
  · refine kostantForm_le_of_root_zsmul _ _ e h ?_ ?_
    · intro i
      obtain ⟨j, rfl⟩ := hσ i
      exact ⟨j, 1, by simp⟩
    · rintro _ ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := hτ i
      exact ⟨j, rfl⟩

/-- A Lie homomorphism with unit-scaled, surjectively renumbered root images and surjectively
renumbered Cartan images maps onto the specified target Kostant form. The ambient Lie map
itself need not be surjective. -/
theorem map_kostantForm_of_root_units (f : L →ₗ⁅ℚ⁆ M)
    (e : ι → L) (h : κ → L) (e' : ι' → M) (h' : κ' → M)
    (σ : ι → ι') (τ : κ → κ') (u : ι → ℤˣ)
    (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (he : ∀ i, f (e i) = (u i : ℤ) • e' (σ i))
    (hh : ∀ i, f (h i) = h' (τ i)) :
    (kostantForm e h).map (map ℚ f).toRingHom = kostantForm e' h' := by
  rw [map_kostantForm]
  simp_rw [he, hh]
  rw [kostantForm_root_units]
  exact kostantForm_reindex e' h' σ τ hσ hτ

/-- Transport between specified Kostant forms along a Lie equivalence whose root images differ
by integral units and surjective renumbering. Cartan vectors are renumbered without rescaling. -/
noncomputable def kostantFormEquivOfRootUnits (f : L ≃ₗ⁅ℚ⁆ M)
    (e : ι → L) (h : κ → L) (e' : ι' → M) (h' : κ' → M)
    (σ : ι → ι') (τ : κ → κ') (u : ι → ℤˣ)
    (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (he : ∀ i, f (e i) = (u i : ℤ) • e' (σ i))
    (hh : ∀ i, f (h i) = h' (τ i)) :
    kostantForm e h ≃+* kostantForm e' h' :=
  (kostantFormEquiv f e h).trans (RingEquiv.subringCongr (by
    have hmap := map_kostantForm_of_root_units f.toLieHom e h e' h' σ τ u hσ hτ he hh
    rw [map_kostantForm] at hmap
    exact hmap))

/-- The integral transport is the induced enveloping-algebra map on underlying elements. -/
@[simp]
theorem coe_kostantFormEquivOfRootUnits_apply (f : L ≃ₗ⁅ℚ⁆ M)
    (e : ι → L) (h : κ → L) (e' : ι' → M) (h' : κ' → M)
    (σ : ι → ι') (τ : κ → κ') (u : ι → ℤˣ)
    (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (he : ∀ i, f (e i) = (u i : ℤ) • e' (σ i))
    (hh : ∀ i, f (h i) = h' (τ i)) (x : kostantForm e h) :
    (kostantFormEquivOfRootUnits f e h e' h' σ τ u hσ hτ he hh x :
      _root_.UniversalEnvelopingAlgebra ℚ M) = map ℚ f.toLieHom x := by
  simp [kostantFormEquivOfRootUnits]

/-- The inverse integral transport is induced by the inverse Lie equivalence. -/
@[simp]
theorem coe_kostantFormEquivOfRootUnits_symm_apply (f : L ≃ₗ⁅ℚ⁆ M)
    (e : ι → L) (h : κ → L) (e' : ι' → M) (h' : κ' → M)
    (σ : ι → ι') (τ : κ → κ') (u : ι → ℤˣ)
    (hσ : Function.Surjective σ) (hτ : Function.Surjective τ)
    (he : ∀ i, f (e i) = (u i : ℤ) • e' (σ i))
    (hh : ∀ i, f (h i) = h' (τ i)) (x : kostantForm e' h') :
    ((kostantFormEquivOfRootUnits f e h e' h' σ τ u hσ hτ he hh).symm x :
      _root_.UniversalEnvelopingAlgebra ℚ L) = map ℚ f.symm.toLieHom x := by
  simp [kostantFormEquivOfRootUnits]

end TauCeti.UniversalEnvelopingAlgebra
