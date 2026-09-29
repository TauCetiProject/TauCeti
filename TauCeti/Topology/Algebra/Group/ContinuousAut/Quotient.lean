/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.ContinuousAut.Characteristic

/-!
# Automorphisms of characteristic quotients

A continuous automorphism of a group with a topology induces an abstract automorphism of each
quotient by a topologically characteristic normal subgroup. These quotient automorphisms are
the coordinates used in the congruence topology on `ContinuousAut G`. Their formula on quotient
classes also shows that inner automorphisms descend to inner automorphisms.

See Ribes–Zalesskii, *Profinite Groups*, §4.4.
-/

public section

namespace TauCeti

namespace ContinuousAut

variable {G : Type*} [Group G] [TopologicalSpace G] {N : Subgroup G}
  (hN : IsTopCharacteristic G N)

/-- The abstract automorphism of a characteristic quotient induced by a continuous
automorphism. For an open normal subgroup this is a coordinate of the congruence topology. -/
def mapQuotient [N.Normal] : ContinuousAut G →* MulAut (G ⧸ N) where
  toFun := fun φ => QuotientGroup.congr N N φ.toMulEquiv
    ((isTopCharacteristic_iff_map_eq.mp hN) φ)
  map_one' := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [ContinuousMulEquiv.toMulEquiv_eq_coe, QuotientGroup.congr_mk,
      MulAut.one_apply]
    change ((1 : ContinuousAut G) x : G ⧸ N) = (x : G ⧸ N)
    rw [ContinuousAut.one_apply]
  map_mul' φ ψ := by
    ext x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [ContinuousMulEquiv.toMulEquiv_eq_coe, QuotientGroup.congr_mk,
      MulAut.mul_apply]
    change (((φ * ψ) x : G) : G ⧸ N) = (φ (ψ x) : G ⧸ N)
    rw [ContinuousAut.mul_apply]

/-- The quotient automorphism sends the class of `x` to the class of `φ x`. -/
@[simp]
theorem mapQuotient_mk [N.Normal] (φ : ContinuousAut G) (x : G) :
    mapQuotient hN φ (x : G ⧸ N) = (φ x : G ⧸ N) :=
  QuotientGroup.congr_mk N N φ.toMulEquiv ((isTopCharacteristic_iff_map_eq.mp hN) φ) x

/-- The quotient coordinate carries conjugation by `g` to conjugation by its class. -/
@[simp]
theorem mapQuotient_conj [SeparatelyContinuousMul G] (g : G) :
    letI := IsTopCharacteristic.normal hN
    mapQuotient hN (conj g) = MulAut.conj (g : G ⧸ N) := by
  have : N.Normal := IsTopCharacteristic.normal hN
  ext x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  simp

end ContinuousAut

end TauCeti
