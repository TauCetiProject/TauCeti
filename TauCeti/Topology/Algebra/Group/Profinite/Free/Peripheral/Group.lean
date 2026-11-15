/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Automorphism
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Permutation

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
* `peripheralAut_le_peripheralPermAut`: peripheral automorphisms are peripheral up to the
  trivial permutation.
* `exponent_eq_iff`: the exponent character is characterized by the peripheral predicate.
* `exponent_surjective`: every unit occurs as an exponent.
* `mem_ker_exponent_iff`: the kernel is the exponent-one part.
* `exponent_conj`: inner automorphisms have exponent one.
* `permData_inclusion`, `permData_fst_eq_one_iff`: in rank at least two, a peripheral automorphism
  has permutation data `(1, exponent φ)`, and the trivial permutation characterizes
  `peripheralAut` inside `peripheralPermAut`.

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
  rw [← isPeripheralPermAut_one_iff] at hφ hψ ⊢
  simpa only [one_mul] using hφ.mul hψ

/-- The inverse of a peripheral automorphism has inverse exponent. -/
theorem IsPeripheralAut.inv (hφ : IsPeripheralAut hF x u φ) :
    IsPeripheralAut hF x u⁻¹ φ⁻¹ := by
  rw [← isPeripheralPermAut_one_iff] at hφ ⊢
  simpa only [inv_one] using hφ.inv

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

/-- Peripheral automorphisms are peripheral up to the trivial permutation. -/
theorem peripheralAut_le_peripheralPermAut (hF : IsProP p F) (x : Fin r → F) :
    peripheralAut hF x ≤ peripheralPermAut hF x := fun φ ⟨u, hu⟩ ↦
  (mem_peripheralPermAut_iff hF x φ).mpr ⟨1, u, (isPeripheralPermAut_one_iff hF x u φ).mpr hu⟩

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
@[simp]
theorem exponent_eq_iff (φ : peripheralAut hF (basis e)) (u : ℤ_[p]ˣ) :
    exponent hF e hr φ = u ↔ IsPeripheralAut hF (basis e) u φ := by
  constructor
  · intro h
    rw [← h]
    exact isPeripheralAut_exponent hF e hr φ
  · exact (isPeripheralAut_exponent hF e hr φ).exponent_unique hr

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

section PermData

variable (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin r)) (hr : 2 ≤ r)

/-- A peripheral automorphism has the trivial permutation, and its exponent, as permutation
data. -/
@[simp]
theorem permData_inclusion (φ : peripheralAut hF (basis e)) :
    permData hF e hr (Subgroup.inclusion (peripheralAut_le_peripheralPermAut hF (basis e)) φ) =
      (1, exponent hF e (zero_lt_two.trans_le hr) φ) :=
  (permData_eq_iff hF e hr _ _ _).mpr <| (isPeripheralPermAut_one_iff hF _ _ _).mpr <|
    isPeripheralAut_exponent hF e _ φ

/-- The permutation of a permutation-peripheral automorphism is trivial exactly when the
automorphism is peripheral. -/
theorem permData_fst_eq_one_iff (φ : peripheralPermAut hF (basis e)) :
    (permData hF e hr φ).1 = 1 ↔ (φ : ContinuousAut F) ∈ peripheralAut hF (basis e) := by
  refine ⟨fun h ↦ ⟨(permData hF e hr φ).2, ?_⟩, fun ⟨u, hu⟩ ↦ ?_⟩
  · rw [← isPeripheralPermAut_one_iff, ← h]
    exact isPeripheralPermAut_permData hF e hr φ
  · rw [(permData_eq_iff hF e hr φ 1 u).mpr ((isPeripheralPermAut_one_iff hF _ _ _).mpr hu)]

end PermData

end TauCeti.Peripheral
