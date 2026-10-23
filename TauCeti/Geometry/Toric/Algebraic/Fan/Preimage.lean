/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Regular

/-!
# Preimages of open subfans

The inverse image of a face-closed subfan under a morphism of finite fans consists of the source
cones whose least target cones belong to the subfan. Least target cones preserve face inclusions,
so this collection is again face-closed. Restricting the original morphism gives a morphism from
the preimage subfan to the chosen target subfan, and the resulting square of fan morphisms
commutes.

These constructions are the combinatorial form of restricting a toric map to the inverse image
of a torus-invariant open subset.

## Main declarations

* `TauCeti.Toric.FanHom.preimageCones`: the cones lying over a chosen face-closed collection.
* `TauCeti.Toric.FanHom.preimageSubfan`: the corresponding subfan of the source.
* `TauCeti.Toric.FanHom.restrictToPreimage`: the restricted morphism of subfans.
* `TauCeti.Toric.FanHom.subfanInclusion_comp_restrictToPreimage`: the commuting square with the
  two subfan inclusions.

## References

* W. Fulton, *Introduction to Toric Varieties*, §2.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.3.
-/

public section

namespace TauCeti.Toric.FanHom

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Phi : Fan i} {Psi : Fan i'}
  (f : FanHom Phi Psi)

/-- The source cones whose least target cones belong to a chosen collection of target cones. -/
def preimageCones (S : Set (PointedCone ℝ V')) : Set (PointedCone ℝ V) :=
  {sigma | ∃ h_sigma : sigma ∈ Phi.cones, f.leastCone h_sigma ∈ S}

/-- A source cone belongs to `preimageCones` exactly when its least target cone belongs to the
chosen collection. -/
@[simp]
theorem mem_preimageCones_iff (S : Set (PointedCone ℝ V')) {sigma : PointedCone ℝ V}
    (h_sigma : sigma ∈ Phi.cones) : sigma ∈ f.preimageCones S ↔ f.leastCone h_sigma ∈ S := by
  constructor
  · rintro ⟨h_sigma', h⟩
    simpa only using h
  · exact fun h ↦ ⟨h_sigma, h⟩

/-- The preimage cones are cones of the source fan. -/
theorem preimageCones_subset (S : Set (PointedCone ℝ V')) :
    f.preimageCones S ⊆ Phi.cones := by
  rintro sigma ⟨h_sigma, -⟩
  exact h_sigma

/-- The preimage of a face-closed collection of target cones is closed under faces. -/
theorem preimageCones_closedUnderFaces (S : Set (PointedCone ℝ V'))
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    ∀ ⦃sigma tau⦄, sigma ∈ f.preimageCones S → tau.IsFaceOf sigma →
      tau ∈ f.preimageCones S := by
  rintro sigma tau ⟨h_sigma, hleast⟩ h_tau_sigma
  exact ⟨Phi.mem_of_isFaceOf h_sigma h_tau_sigma,
    hface hleast (f.leastCone_isFaceOf h_sigma h_tau_sigma)⟩

/-- The preimage of a face-closed subfan under a fan morphism. Its cones are precisely those
whose least target cones lie in the chosen target subfan. -/
noncomputable abbrev preimageSubfan (S : Set (PointedCone ℝ V'))
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) : Fan i :=
  Phi.subfan (f.preimageCones S) (f.preimageCones_subset S)
    (f.preimageCones_closedUnderFaces S hface)

/-- Every cone of the preimage subfan is a cone of the source fan. -/
theorem preimageSubfan_cones_subset (S : Set (PointedCone ℝ V'))
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)
    : (f.preimageSubfan S hface).cones ⊆ Phi.cones := by
  rw [Fan.subfan_cones]
  exact f.preimageCones_subset S

/-- The preimage subfan uses the source fan's integral lattice. -/
@[simp]
theorem preimageSubfan_lattice (S : Set (PointedCone ℝ V'))
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    (f.preimageSubfan S hface).lattice = Phi.lattice := (rfl)

/-- Restrict a fan morphism to the preimage of a face-closed target subfan. -/
noncomputable def restrictToPreimage (S : Set (PointedCone ℝ V')) (hS : S ⊆ Psi.cones)
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    FanHom (f.preimageSubfan S hface) (Psi.subfan S hS hface) where
  latticeMap := f.latticeMap
  realMap := f.realMap
  map_lattice := f.map_lattice
  map_cone sigma h_sigma := by
    rw [Fan.subfan_cones] at h_sigma
    obtain ⟨h_sigma_Phi, hleast⟩ := h_sigma
    exact ⟨f.leastCone h_sigma_Phi, by simpa only [Fan.subfan_cones] using hleast,
      f.map_le_leastCone h_sigma_Phi⟩

/-- Restriction to a preimage subfan does not change the integral lattice map. -/
@[simp]
theorem restrictToPreimage_latticeMap (S : Set (PointedCone ℝ V')) (hS : S ⊆ Psi.cones)
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    (f.restrictToPreimage S hS hface).latticeMap = f.latticeMap := (rfl)

/-- Restriction to a preimage subfan does not change the ambient real-linear map. -/
@[simp]
theorem restrictToPreimage_realMap (S : Set (PointedCone ℝ V')) (hS : S ⊆ Psi.cones)
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    (f.restrictToPreimage S hS hface).realMap = f.realMap := (rfl)

/-- The least cone of the restricted map is the original least cone. -/
@[simp]
theorem restrictToPreimage_leastCone (S : Set (PointedCone ℝ V')) (hS : S ⊆ Psi.cones)
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S)
    (sigma : (f.preimageSubfan S hface).cones) :
    (f.restrictToPreimage S hS hface).leastCone sigma.2 =
      f.leastCone (f.preimageSubfan_cones_subset S hface sigma.2) := by
  have h_sigma_preimage : sigma.1 ∈ f.preimageCones S := by
    simpa only [Fan.subfan_cones] using sigma.2
  obtain ⟨h_sigma, hleast⟩ := h_sigma_preimage
  apply le_antisymm
  · apply (f.restrictToPreimage S hS hface).leastCone_le sigma.2
      (by simpa only [Fan.subfan_cones] using hleast)
    exact f.map_le_leastCone h_sigma
  · apply f.leastCone_le h_sigma
      (hS (by simpa only [Fan.subfan_cones] using
        (f.restrictToPreimage S hS hface).leastCone_mem sigma.2))
    simpa only [restrictToPreimage_realMap] using
      (f.restrictToPreimage S hS hface).map_le_leastCone sigma.2

/-- Restricting a fan morphism to an open subfan commutes with the source and target subfan
inclusions. -/
theorem subfanInclusion_comp_restrictToPreimage
    (S : Set (PointedCone ℝ V')) (hS : S ⊆ Psi.cones)
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    (Psi.subfanInclusion S hS hface).comp (f.restrictToPreimage S hS hface) =
      f.comp (Phi.subfanInclusion (f.preimageCones S) (f.preimageCones_subset S)
        (f.preimageCones_closedUnderFaces S hface)) := by
  apply FanHom.ext
  simp

end TauCeti.Toric.FanHom

namespace TauCeti.Toric.Fan.IsRegular

universe u

variable {N N' V V' : Type u} [AddCommGroup N] [AddCommGroup N']
  [AddCommGroup V] [AddCommGroup V'] [Module ℝ V] [Module ℝ V']
  {i : N →+ V} {i' : N' →+ V'} {Phi : Fan i} {Psi : Fan i'}

/-- The preimage subfan of a regular fan is regular. -/
theorem preimageSubfan (hPhi : Phi.IsRegular) (f : FanHom Phi Psi)
    (S : Set (PointedCone ℝ V'))
    (hface : ∀ ⦃sigma tau⦄, sigma ∈ S → tau.IsFaceOf sigma → tau ∈ S) :
    (f.preimageSubfan S hface).IsRegular :=
  hPhi.subfan (f.preimageCones S) (f.preimageCones_subset S)
    (f.preimageCones_closedUnderFaces S hface)

end TauCeti.Toric.Fan.IsRegular
