/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Automorphism

/-!
# The peripheral automorphism group and its exponent character

The continuous automorphisms preserving every peripheral conjugacy class up to a common
unit power form a subgroup `peripheralAut`. This construction applies to any finite family
in a pro-`p` group, including its cusp. Composition multiplies the exponents and inversion
inverts them.

For a marked free pro-`p` group of positive rank, the exponent is uniquely determined and
defines the homomorphism `exponent` to `ℤ_[p]ˣ`. The peripheral-power theorem makes this
character surjective. Its kernel consists precisely of the automorphisms preserving each
peripheral conjugacy class without a power; in particular, it contains the inner
automorphisms. This character is the algebraic input to studying peripheral automorphisms
as a topological group and splitting their exponent over principal units.

## Main results

* `IsPeripheralAut.mul`, `IsPeripheralAut.inv`: the laws for peripheral exponents.
* `mem_peripheralAut_iff`: membership is the existence of a peripheral exponent.
* `exponent_eq_iff`: the exponent character is characterized by the peripheral predicate.
* `exponent_surjective`: every unit occurs as an exponent.
* `mem_ker_exponent_iff`: the kernel is the exponent-one part.
* `exponent_conj`: inner automorphisms have exponent one.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for peripheral automorphisms of free pro-`p` groups and their common exponent.
-/

public section

namespace TauCeti.Peripheral

variable {p r : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

section Subgroup

variable {hF : IsProP p F} {x : Fin r → F} {u v : ℤ_[p]ˣ}
  {φ ψ : ContinuousAut F}

/-- Composition of peripheral automorphisms multiplies their exponents. -/
theorem IsPeripheralAut.mul (hφ : IsPeripheralAut hF x u φ)
    (hψ : IsPeripheralAut hF x v ψ) : IsPeripheralAut hF x (u * v) (φ * ψ) := by
  rw [isPeripheralAut_iff] at hφ hψ ⊢
  have h (y : F) (hφ : IsConj (hF.padicPow y u) (φ y))
      (hψ : IsConj (hF.padicPow y v) (ψ y)) :
      IsConj (hF.padicPow y ↑(u * v)) ((φ * ψ) y) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hφ
    have hpow : IsConj (hF.padicPow y ↑(u * v)) (hF.padicPow (φ y) v) := by
      apply isConj_iff.mpr
      refine ⟨g, ?_⟩
      rw [← hg, hF.conj_padicPow, ← hF.padicPow_mul, Units.val_mul]
    have hmap := (φ : F →* F).map_isConj hψ
    rw [hF.map_padicPow hF (φ : F →* F) φ.continuous] at hmap
    exact hpow.trans hmap
  exact ⟨fun i ↦ h (x i) (hφ.1 i) (hψ.1 i), h (cusp x) hφ.2 hψ.2⟩

/-- The inverse of a peripheral automorphism has inverse exponent. -/
theorem IsPeripheralAut.inv (hφ : IsPeripheralAut hF x u φ) :
    IsPeripheralAut hF x u⁻¹ φ⁻¹ := by
  rw [isPeripheralAut_iff] at hφ ⊢
  have h (y : F) (hφ : IsConj (hF.padicPow y u) (φ y)) :
      IsConj (hF.padicPow y ↑u⁻¹) (φ⁻¹ y) := by
    have hmap := (φ.symm : F →* F).map_isConj hφ
    simp only [MonoidHom.coe_ofClass, ContinuousMulEquiv.symm_apply_apply] at hmap
    obtain ⟨g, hg⟩ := isConj_iff.mp hmap.symm
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    rw [← hF.conj_padicPow, hg, ContinuousAut.inv_apply]
    simpa only [MonoidHom.coe_ofClass, hF.padicPow_padicPow_inv] using
      (hF.map_padicPow hF (φ.symm : F →* F) φ.symm.continuous
        (hF.padicPow y u) ↑u⁻¹).symm
  exact ⟨fun i ↦ h (x i) (hφ.1 i), h (cusp x) hφ.2⟩

/-- The continuous automorphisms peripheral for `x` with some common unit exponent. -/
def peripheralAut (hF : IsProP p F) (x : Fin r → F) : Subgroup (ContinuousAut F) where
  carrier := {φ | ∃ u : ℤ_[p]ˣ, IsPeripheralAut hF x u φ}
  one_mem' := ⟨1, isPeripheralAut_one hF x⟩
  mul_mem' := by
    rintro φ ψ ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u * v, hu.mul hv⟩
  inv_mem' := by
    rintro φ ⟨u, hu⟩
    exact ⟨u⁻¹, hu.inv⟩

/-- Membership in the peripheral automorphism group means admitting a unit exponent. -/
@[simp]
theorem mem_peripheralAut_iff (hF : IsProP p F) (x : Fin r → F) (φ : ContinuousAut F) :
    φ ∈ peripheralAut hF x ↔ ∃ u : ℤ_[p]ˣ, IsPeripheralAut hF x u φ :=
  (Iff.rfl)

/-- Every inner automorphism belongs to the peripheral automorphism group. -/
theorem range_conj_le_peripheralAut (hF : IsProP p F) (x : Fin r → F) :
    (ContinuousAut.conj : F →* ContinuousAut F).range ≤ peripheralAut hF x := by
  rintro _ ⟨g, rfl⟩
  exact ⟨1, isPeripheralAut_conj hF x g⟩

/-- Inner automorphisms viewed as peripheral automorphisms. -/
def conj (hF : IsProP p F) (x : Fin r → F) : F →* peripheralAut hF x :=
  ContinuousAut.conj.codRestrict _ fun g ↦ ⟨1, isPeripheralAut_conj hF x g⟩

@[simp]
theorem coe_conj (hF : IsProP p F) (x : Fin r → F) (g : F) :
    (conj hF x g : ContinuousAut F) = ContinuousAut.conj g :=
  (rfl)

end Subgroup

section Exponent

variable (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (hr : 0 < r)

/-- The unique common unit exponent of a peripheral automorphism of a marked free
pro-`p` group of positive rank. -/
noncomputable def exponent : peripheralAut hF (basis e) →* ℤ_[p]ˣ where
  toFun φ := Classical.choose φ.property
  map_one' := (Classical.choose_spec
    (1 : peripheralAut hF (basis e)).property).exponent_unique hr
      (isPeripheralAut_one hF (basis e))
  map_mul' φ ψ := (Classical.choose_spec (φ * ψ).property).exponent_unique hr
    ((Classical.choose_spec φ.property).mul (Classical.choose_spec ψ.property))

/-- The exponent character supplies a peripheral exponent for its argument. -/
theorem isPeripheralAut_exponent (φ : peripheralAut hF (basis e)) :
    IsPeripheralAut hF (basis e) (exponent hF e hr φ) φ :=
  Classical.choose_spec φ.property

/-- The exponent of a peripheral automorphism is `u` exactly when it is peripheral of
exponent `u`. -/
theorem exponent_eq_iff (φ : peripheralAut hF (basis e)) (u : ℤ_[p]ˣ) :
    exponent hF e hr φ = u ↔ IsPeripheralAut hF (basis e) u φ := by
  constructor
  · intro h
    rw [← h]
    exact isPeripheralAut_exponent hF e hr φ
  · exact (isPeripheralAut_exponent hF e hr φ).exponent_unique hr

/-- The exponent is `u` exactly when the images of the basis and cusp are conjugate to
their `u`-th powers. -/
@[simp]
theorem exponent_eq_iff_isConj (φ : peripheralAut hF (basis e)) (u : ℤ_[p]ˣ) :
    exponent hF e hr φ = u ↔
      (∀ i, IsConj (hF.padicPow (basis e i) u) ((φ : ContinuousAut F) (basis e i))) ∧
        IsConj (hF.padicPow (cusp (basis e)) u) ((φ : ContinuousAut F) (cusp (basis e))) := by
  rw [exponent_eq_iff, isPeripheralAut_iff]

/-- Every unit of `ℤ_[p]` is an exponent of a peripheral automorphism. -/
theorem exponent_surjective : Function.Surjective (exponent hF e hr) := by
  intro u
  obtain ⟨φ, hφ⟩ := exists_isPeripheralAut hF e u
  exact ⟨⟨φ, u, hφ⟩, (exponent_eq_iff hF e hr _ u).mpr hφ⟩

/-- The kernel consists exactly of the automorphisms preserving all peripheral
conjugacy classes with exponent one. -/
theorem mem_ker_exponent_iff (φ : peripheralAut hF (basis e)) :
    φ ∈ (exponent hF e hr).ker ↔ IsPeripheralAut hF (basis e) 1 φ := by
  rw [MonoidHom.mem_ker, exponent_eq_iff]

/-- Inner automorphisms have exponent one. -/
@[simp]
theorem exponent_conj (g : F) : exponent hF e hr (conj hF (basis e) g) = 1 :=
  (exponent_eq_iff hF e hr _ 1).mpr (isPeripheralAut_conj hF (basis e) g)

end Exponent

end TauCeti.Peripheral
