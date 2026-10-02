/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.PadicInt
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Topology
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Procyclic

/-!
# Peripheral automorphisms in rank one

Let `F` be a free pro-`p` group of rank one, presented by a marked isomorphism
`e : F ≃ₜ* freeProP p (Fin 1)`, with basis element `x = basis e 0`. Then `F` is isomorphic to
`ℤ_[p]`, hence commutative, so its conjugacy classes are singletons, and the cusp is `x⁻¹`. The
peripheral conditions therefore collapse: a continuous automorphism is peripheral of exponent `u`
exactly when it sends `x` to `x ^ u`.

Every continuous automorphism `φ` is of this form. Its value `φ x` topologically generates `F`,
and two topological generators of a procyclic pro-`p` group differ by a unit exponent. So in rank
one the peripheral automorphism group is all of `ContinuousAut F`, and the exponent character is
injective, since an automorphism is determined by its value on `x`. Together with the
peripheral-power theorem this identifies `ContinuousAut F` with `ℤ_[p]ˣ`: the exponent is a
topological group isomorphism `ContinuousAut F ≃ₜ* ℤ_[p]ˣ`, whose inverse sends `u` to the
automorphism `x ↦ x ^ u`.

## Main definitions

* `TauCeti.Peripheral.continuousAutEquivUnits`: for a marked free pro-`p` group of rank one, the
  topological group isomorphism `ContinuousAut F ≃ₜ* ℤ_[p]ˣ` sending `φ` to the unit `u` with
  `φ x = x ^ u`.

## Main results

* `TauCeti.Peripheral.isConj_iff_eq_rank_one`: conjugacy in `F` is equality.
* `TauCeti.Peripheral.isPeripheralAut_iff_apply_basis_eq_padicPow_rank_one`: an automorphism is
  peripheral of exponent `u` exactly when it sends `x` to `x ^ u`.
* `TauCeti.Peripheral.exists_isPeripheralAut_rank_one`,
  `TauCeti.Peripheral.mem_peripheralAut_rank_one`,
  `TauCeti.Peripheral.peripheralAut_eq_top_rank_one`: every continuous automorphism is peripheral.
* `TauCeti.Peripheral.exponent_bijective_rank_one`: the exponent character is bijective.
* `TauCeti.Peripheral.apply_basis_continuousAutEquivUnits`,
  `TauCeti.Peripheral.continuousAutEquivUnits_eq_iff`: the isomorphism with `ℤ_[p]ˣ` is
  characterized by `φ x = x ^ u`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 4.3 for procyclic pro-`p`
  groups and Section 4.5 for automorphisms of free pro-`p` groups.
-/

public section

namespace TauCeti.Peripheral

variable {p : ℕ} {F : Type*} [Group F] [TopologicalSpace F]

/-- In rank one the basis element topologically generates `F`. -/
theorem topologicalClosure_closure_basis_zero [IsTopologicalGroup F]
    (e : F ≃ₜ* freeProP p (Fin 1)) :
    (Subgroup.closure ({basis e 0} : Set F)).topologicalClosure = ⊤ := by
  have h := topologicalClosure_closure_range_basis e
  rwa [Set.range_unique] at h

/-- In a free pro-`p` group of rank one, conjugacy is equality: the group is commutative. -/
theorem isConj_iff_eq_rank_one [Fact p.Prime] (e : F ≃ₜ* freeProP p (Fin 1)) {y z : F} :
    IsConj y z ↔ y = z := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ IsConj.refl y⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have hc : c * y = y * c := e.injective (by simpa using (freeProP.commute_of_unique _ _).eq)
  rw [hc, mul_inv_cancel_right]

variable [Fact p.Prime] [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]
  (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin 1))

/-- **Peripheral automorphisms in rank one.** A continuous automorphism of a free pro-`p` group of
rank one is peripheral of exponent `u` exactly when it sends the basis element `x` to `x ^ u`. -/
theorem isPeripheralAut_iff_apply_basis_eq_padicPow_rank_one (u : ℤ_[p]ˣ) (φ : ContinuousAut F) :
    IsPeripheralAut hF (basis e) u φ ↔ φ (basis e 0) = hF.padicPow (basis e 0) u := by
  simp only [isPeripheralAut_iff, isConj_iff_eq_rank_one e, Fin.forall_fin_one, cusp_fin_one,
    map_inv, hF.inv_padicPow, inv_inj, and_self]
  exact eq_comm

/-- **Every automorphism is peripheral in rank one.** A continuous automorphism of a free pro-`p`
group of rank one sends the basis element `x` to a topological generator, which is `x ^ u` for a
unit `u`, and it is then peripheral of exponent `u`. -/
theorem exists_isPeripheralAut_rank_one (φ : ContinuousAut F) :
    ∃ u : ℤ_[p]ˣ, IsPeripheralAut hF (basis e) u φ := by
  -- the image of a topological generator under a surjective continuous homomorphism
  have hgen : (Subgroup.closure ({φ (basis e 0)} : Set F)).topologicalClosure = ⊤ := by
    rw [← Set.image_singleton]
    exact topologicalClosure_closure_image_eq_top (topologicalClosure_closure_basis_zero e)
      (f := (φ : F →* F)) φ.continuous φ.surjective.denseRange
  obtain ⟨l, hl, hφ⟩ :=
    hF.exists_isUnit_padicPow_eq_of_topologicalClosure_closure_eq_top
      (topologicalClosure_closure_basis_zero e) hgen
  exact ⟨hl.unit, (isPeripheralAut_iff_apply_basis_eq_padicPow_rank_one hF e _ φ).mpr hφ.symm⟩

/-- In rank one every continuous automorphism is a peripheral automorphism. -/
theorem mem_peripheralAut_rank_one (φ : ContinuousAut F) : φ ∈ peripheralAut hF (basis e) :=
  (mem_peripheralAut_iff hF (basis e) φ).mpr (exists_isPeripheralAut_rank_one hF e φ)

/-- In rank one the peripheral automorphism group is the whole group of continuous
automorphisms. -/
theorem peripheralAut_eq_top_rank_one : peripheralAut hF (basis e) = ⊤ :=
  eq_top_iff.mpr fun φ _ ↦ mem_peripheralAut_rank_one hF e φ

/-- In rank one a peripheral automorphism `φ` sends the basis element `x` to `x ^ u`, with `u` its
exponent. -/
theorem apply_basis_exponent_rank_one (φ : peripheralAut hF (basis e)) :
    (φ : ContinuousAut F) (basis e 0) = hF.padicPow (basis e 0) (exponent hF e one_pos φ) :=
  (isPeripheralAut_iff_apply_basis_eq_padicPow_rank_one hF e _ _).mp
    (isPeripheralAut_exponent hF e one_pos φ)

/-- **The exponent character is bijective in rank one.** It is injective because an automorphism
is determined by its value `x ^ u` on the basis element, and surjective by the peripheral-power
theorem. -/
theorem exponent_bijective_rank_one : Function.Bijective (exponent hF e one_pos) := by
  refine ⟨fun φ ψ h ↦ Subtype.ext <| ContinuousMulEquiv.ext fun y ↦ ?_,
    exponent_surjective hF e one_pos⟩
  -- two continuous endomorphisms agreeing on the basis agree everywhere
  refine DFunLike.congr_fun (hom_ext_basis (f := ((φ : ContinuousAut F) : F →ₜ* F))
    (g := ((ψ : ContinuousAut F) : F →ₜ* F)) e fun i ↦ ?_) y
  rw [Subsingleton.elim i 0]
  exact (apply_basis_exponent_rank_one hF e φ).trans
    (h ▸ (apply_basis_exponent_rank_one hF e ψ).symm)

/-- **The continuous automorphisms of a free pro-`p` group of rank one are the units of
`ℤ_[p]`.** The topological group isomorphism `ContinuousAut F ≃ₜ* ℤ_[p]ˣ` sending a continuous
automorphism `φ` to the unique unit `u` with `φ x = x ^ u`, for the basis element `x`. It is the
exponent character, every automorphism being peripheral in rank one. -/
noncomputable def continuousAutEquivUnits : ContinuousAut F ≃ₜ* ℤ_[p]ˣ :=
  have hmem := mem_peripheralAut_rank_one hF e
  -- the exponent character, precomposed with the identification of `peripheralAut` with `⊤`
  let f : ContinuousAut F →* ℤ_[p]ˣ :=
    (exponent hF e one_pos).comp ((MonoidHom.id _).codRestrict _ hmem)
  have hf : Function.Bijective f :=
    (exponent_bijective_rank_one hF e).comp
      ⟨fun _ _ h ↦ congrArg Subtype.val h, fun φ ↦ ⟨φ, rfl⟩⟩
  have hcont : Continuous f :=
    (continuous_exponent hF e one_pos).comp (continuous_id.subtype_mk hmem)
  have := ContinuousAut.compactSpace
    ((isTopologicallyFinitelyGenerated_congr e).mpr (isTopologicallyFinitelyGenerated_freeProP p _))
  -- a continuous bijection from a compact space to a Hausdorff space is a homeomorphism
  (MulEquiv.ofBijective f hf).toContinuousMulEquiv fun _ ↦
    (hcont.homeoOfEquivCompactToT2 (f := (MulEquiv.ofBijective f hf).toEquiv)).isOpen_preimage

/-- On peripheral automorphisms, the isomorphism with `ℤ_[p]ˣ` is the exponent character. -/
@[simp]
theorem continuousAutEquivUnits_coe (φ : peripheralAut hF (basis e)) :
    continuousAutEquivUnits hF e φ = exponent hF e one_pos φ :=
  (rfl)

/-- The image of `φ` in `ℤ_[p]ˣ` is `u` exactly when `φ` sends the basis element `x` to `x ^ u`. -/
theorem continuousAutEquivUnits_eq_iff (φ : ContinuousAut F) (u : ℤ_[p]ˣ) :
    continuousAutEquivUnits hF e φ = u ↔ φ (basis e 0) = hF.padicPow (basis e 0) u := by
  have h := exponent_eq_iff hF e one_pos ⟨φ, mem_peripheralAut_rank_one hF e φ⟩ u
  rwa [← continuousAutEquivUnits_coe, isPeripheralAut_iff_apply_basis_eq_padicPow_rank_one] at h

/-- The automorphism `φ` sends the basis element `x` to `x ^ u`, where `u` is its image in
`ℤ_[p]ˣ`. -/
theorem apply_basis_continuousAutEquivUnits (φ : ContinuousAut F) :
    φ (basis e 0) = hF.padicPow (basis e 0) (continuousAutEquivUnits hF e φ) :=
  (continuousAutEquivUnits_eq_iff hF e φ _).mp rfl

/-- The inverse isomorphism sends a unit `u` to the automorphism `x ↦ x ^ u`. -/
@[simp]
theorem continuousAutEquivUnits_symm_apply_basis (u : ℤ_[p]ˣ) :
    (continuousAutEquivUnits hF e).symm u (basis e 0) = hF.padicPow (basis e 0) u := by
  rw [apply_basis_continuousAutEquivUnits hF e, ContinuousMulEquiv.apply_symm_apply]

end TauCeti.Peripheral
