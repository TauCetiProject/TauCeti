/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Galois
import TauCeti.RingTheory.Perfection

/-!
# Compatible division points of a Tate curve

A compatible family `uₖ` of `ℓ^k`-th roots of the Tate parameter determines a point of the
Tate module whose exponent is one at every level. Such a point exists whenever the `ℓ`-th
power map on the extension's units is surjective, in particular over an algebraically closed
complete ultrametric extension for `ℓ ≠ 0`. Choosing roots independently at each level would
not suffice: the compatibility `uₖ₊₁ ^ ℓ = uₖ` is essential.

The action of a continuous `K`-automorphism `σ` on this Tate-module point detects exactly its
action on the entire root family. In particular, the root-of-unity displacement formulas at
finite level detect genuine nontrivial action on the Tate module, not only on an isolated
torsion group. This is the
Kummer direction complementary to the cyclotomic direction in Tate-curve monodromy.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
-/

public noncomputable section

namespace TauCeti

open Function WeierstrassCurve WeierstrassCurve.Affine
open scoped AddSubgroup Pointwise

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] [DecidableEq L] (q : Kˣ) (hq : ‖(q : K)‖ < 1)
  (ℓ : ℕ)

/-- Raising a root of the Tate parameter to the `ℓ`-th power gives the preceding
level's division point under the Tate-module transition. -/
@[simp]
theorem tateModuleTransition_tateDivisionPoint (k : ℕ) (v : Lˣ)
    (hv : v ^ (ℓ ^ (k + 1)) = Units.map (algebraMap K L : K →* L) q) :
    tateModuleTransition ℓ (((tateCurveAt q hq)⁄L).toAffine.Point) k
        (tateDivisionPoint q hq (ℓ ^ (k + 1)) v hv) =
      tateDivisionPoint q hq (ℓ ^ k) (v ^ ℓ) (by rw [← pow_mul, ← pow_succ', hv]) := by
  apply Subtype.ext
  simp only [tateModuleTransition_apply, coe_tateDivisionPoint]
  rw [← map_nsmul, ← ofMul_pow]

/-- A nonzero level-`k` exponent obstructs divisibility by `ℓ ^ k` in the Tate module. -/
theorem ne_pow_nsmul_of_tateTorsionExponent_proj_ne_zero (k : ℕ)
    {x : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point)}
    (hx : tateTorsionExponent L q hq (ℓ ^ k) (TateModule.proj k x) ≠ 0)
    (y : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point)) : x ≠ ℓ ^ k • y := by
  intro h
  have hy : ℓ ^ k • TateModule.proj k y = 0 :=
    AddSubgroup.torsionBy.nsmul (TateModule.proj k y)
  apply hx
  rw [h, map_nsmul, hy, map_zero]

variable (u : ℕ → Lˣ)
  (hu : ∀ k, u k ^ (ℓ ^ k) = Units.map (algebraMap K L : K →* L) q)
  (hcompat : ∀ k, u (k + 1) ^ ℓ = u k)

/-- The Tate-module point determined by a compatible tower of roots of the parameter.
Its finite-level exponent is one, rather than zero as in the roots-of-unity direction. -/
def tateDivisionTower : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point) :=
  TateModule.mk (fun k ↦ tateDivisionPoint q hq (ℓ ^ k) (u k) (hu k))
    (fun k ↦ by simp only [tateModuleTransition_tateDivisionPoint, hcompat])

/-- The components of the compatible division point are the prescribed division points. -/
@[simp]
theorem proj_tateDivisionTower (k : ℕ) :
    TateModule.proj k (tateDivisionTower q hq ℓ u hu hcompat) =
      tateDivisionPoint q hq (ℓ ^ k) (u k) (hu k) := by
  rw [tateDivisionTower, TateModule.proj_mk]

/-- When `ℓ ≠ 1`, the compatible division point is primitive: it is not an `ℓ`-multiple in the
Tate module. Thus it supplies an integral, not merely rational, Kummer direction. -/
theorem tateDivisionTower_ne_nsmul (hℓ : ℓ ≠ 1)
    (y : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point)) :
    tateDivisionTower q hq ℓ u hu hcompat ≠ ℓ • y := by
  have hx : tateTorsionExponent L q hq (ℓ ^ 1)
      (TateModule.proj 1 (tateDivisionTower q hq ℓ u hu hcompat)) ≠ 0 := by
    rw [proj_tateDivisionTower, tateTorsionExponent_tateDivisionPoint, pow_one]
    intro he
    have hm : (1 : ℤ) ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ ℤ) := by
      rw [← Submodule.Quotient.mk_eq_zero, Ideal.Quotient.mk_eq_mk, map_one]
      exact he
    obtain ⟨a, -, ha⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hm
    have hd : (ℓ : ℤ) ∣ 1 := ⟨a, ha.symm⟩
    exact hℓ (Nat.dvd_one.mp (by exact_mod_cast hd))
  simpa only [pow_one] using
    ne_pow_nsmul_of_tateTorsionExponent_proj_ne_zero q hq ℓ 1 hx y

section Galois

variable [Fact ℓ.Prime] (σ : L ≃ₐ[K] L) (hσ : Continuous σ)

private theorem proj_tateModuleGaloisRepresentation_tateDivisionTower (k : ℕ) :
    TateModule.proj k
        (((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ)
          (tateDivisionTower q hq ℓ u hu hcompat)) =
      torsionByMap ((ℓ ^ k : ℕ) : ℤ) (Point.map σ.toAlgHom).toIntLinearMap
        (tateDivisionPoint q hq (ℓ ^ k) (u k) (hu k)) := by
  apply Subtype.ext
  simp only [coe_proj_tateModuleGaloisRepresentation, proj_tateDivisionTower,
    coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap]

include hσ

/-- For a continuous `K`-automorphism `σ`, at every level the displacement of the compatible
division point is represented by `σ(uₖ)/uₖ`. The equation specifying the root of unity avoids
any choice of its generator. -/
theorem proj_tateModuleGaloisRepresentation_tateDivisionTower_sub (k : ℕ)
    (ζ : rootsOfUnity (ℓ ^ k) L)
    (hζ : Units.map (σ : L →* L) (u k) = (ζ : Lˣ) * u k) :
    TateModule.proj k
        (((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ)
          (tateDivisionTower q hq ℓ u hu hcompat) - tateDivisionTower q hq ℓ u hu hcompat) =
      tateRootsOfUnityHom L q hq (ℓ ^ k) (.ofMul ζ) := by
  rw [map_sub, proj_tateModuleGaloisRepresentation_tateDivisionTower, proj_tateDivisionTower]
  exact torsionByMap_tateDivisionPoint_sub q hq (ℓ ^ k) σ.toAlgHom hσ _ _ ζ hζ

/-- A continuous `K`-automorphism fixes the compatible division point exactly when it fixes
every root in the chosen tower. Thus a nontrivial Kummer action cannot disappear in the inverse
limit. -/
theorem tateModuleGaloisRepresentation_tateDivisionTower_eq_self_iff :
    ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ)
        (tateDivisionTower q hq ℓ u hu hcompat) = tateDivisionTower q hq ℓ u hu hcompat ↔
      ∀ k, Units.map (σ : L →* L) (u k) = u k := by
  constructor
  · intro h k
    have hk := congrArg (TateModule.proj k) h
    rw [proj_tateModuleGaloisRepresentation_tateDivisionTower, proj_tateDivisionTower] at hk
    exact (torsionByMap_tateDivisionPoint_eq_self_iff q hq (ℓ ^ k) σ.toAlgHom hσ _ _).mp hk
  · intro h
    apply TateModule.ext
    intro k
    rw [proj_tateModuleGaloisRepresentation_tateDivisionTower, proj_tateDivisionTower]
    exact (torsionByMap_tateDivisionPoint_eq_self_iff q hq (ℓ ^ k) σ.toAlgHom hσ _ _).mpr (h k)

end Galois

variable (L)

/-- If the `ℓ`-th power map on the extension's units is surjective, there is a Tate-module
point whose exponent is one at every level. In particular, the levelwise surjectivity of the
exponent maps is realized by compatible preimages of one. -/
theorem exists_forall_tateTorsionExponent_proj_eq_one
    (hℓ : Surjective fun v : Lˣ ↦ v ^ ℓ) :
    ∃ x : TateModule ℓ (((tateCurveAt q hq)⁄L).toAffine.Point), ∀ k,
      tateTorsionExponent L q hq (ℓ ^ k) (TateModule.proj k x) =
        (1 : QuotSMulTop ((ℓ ^ k : ℕ) : ℤ) ℤ) := by
  obtain ⟨u, hu₀⟩ := Perfection.coeffMonoidHom_surjective
    hℓ 0
    (Units.map (algebraMap K L : K →* L) q)
  refine ⟨tateDivisionTower q hq ℓ (fun k ↦ Perfection.coeffMonoidHom Lˣ ℓ k u)
    (fun k ↦ (Perfection.coeffMonoidHom_pow_p_pow_self u k).trans hu₀)
    (Perfection.coeffMonoidHom_pow_p' u), ?_⟩
  intro k
  rw [proj_tateDivisionTower, tateTorsionExponent_tateDivisionPoint]

end TauCeti
