/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Galois

/-!
# Galois action on Tate-curve torsion

For a Tate curve with parameter `q`, the exponent quotient of its `n`-torsion is fixed by
continuous automorphisms of the coefficient extension. Consequently every displacement
`σ(P) - P` lies in the roots-of-unity subgroup. If `σ` also fixes the `n`-th roots of unity,
then `(σ - 1)² = 0` on `E_q[n]`. Fixing all `ℓ`-power roots of unity gives the same
basis-free identity on the `ℓ`-adic Tate module.

A chosen `n`-th root `u` of `q` gives a torsion point of exponent one. Its displacement is
exactly the root-of-unity point with parameter `σ(u)/u`; for `n ≠ 0`, this displacement
vanishes exactly when `σ(u) = u`. These formulas describe the finite-level extension of the
trivial character by the cyclotomic character, used in the inertia calculation at split
multiplicative reduction. They hold over complete ultrametric extensions, without assuming
that every exponent class is represented or that all roots of unity are rational.

When an `n`-th root of the parameter is chosen, two continuous coefficient maps into any
complete ultrametric extension induce the same map on `n`-torsion exactly when they agree
on the roots of unity and the chosen parameter root. In particular, this detects triviality
of the entire torsion action. If roots of unity are fixed, every displacement is its exponent
times the displacement of the chosen division point.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
-/

public section

noncomputable section

namespace TauCeti

open Function WeierstrassCurve WeierstrassCurve.Affine
open scoped AddSubgroup

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {L : Type*} [NormedField L] [NormedAlgebra K L] [CompleteSpace L]
  [IsUltrametricDist L] [DecidableEq L] (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℕ)

/-- Every displacement of a Tate torsion point under a continuous algebra endomorphism belongs
to the roots-of-unity image. No surjectivity assumption on the exponent map is needed. -/
theorem sub_mem_range_tateRootsOfUnityHom (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (P : (((tateCurveAt q hq)⁄L).toAffine.Point)[(n : ℤ)]) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap P - P ∈
      (tateRootsOfUnityHom L q hq n).range := by
  apply (exact_tateRootsOfUnityHom_tateTorsionExponent L q hq n _).mp
  rw [map_sub, tateTorsionExponent_torsionByMap q hq n σ hσ, sub_self]

/-- A continuous algebra endomorphism fixing the `n`-th roots of unity acts unipotently of index
at most two on Tate-curve `n`-torsion. This is an identity of endomorphisms, not a choice of a
torsion basis. -/
theorem torsionByMap_tateCurveAt_sub_id_sq_eq_zero (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (hζ : ∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = ζ) :
    (torsionByMap (n : ℤ)
      (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap -
        LinearMap.id) ^ 2 = 0 := by
  apply LinearMap.ext
  intro P
  obtain ⟨ζ, hP⟩ := sub_mem_range_tateRootsOfUnityHom q hq n σ hσ P
  obtain ⟨ζ, rfl⟩ := Additive.ofMul.surjective ζ
  have hfix := torsionByMap_tateRootsOfUnityHom q hq n σ hσ ζ
  rw [hζ ζ] at hfix
  simp only [pow_two, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.id_apply,
    LinearMap.zero_apply, ← hP, hfix, sub_self]

/-- The displacement of a chosen division point is the root-of-unity point with parameter
`σ(u)/u`. The equation `σ(u) = ζ u` specifies this root without choosing a generator of `μ_n`. -/
theorem torsionByMap_tateDivisionPoint_sub (σ : L →ₐ[K] L) (hσ : Continuous σ)
    (u : Lˣ) (hu : u ^ n = Units.map (algebraMap K L : K →* L) q)
    (ζ : rootsOfUnity n L)
    (hζ : Units.map (σ : L →* L) u = (ζ : Lˣ) * u) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
        (tateDivisionPoint q hq n u hu) - tateDivisionPoint q hq n u hu =
      tateRootsOfUnityHom L q hq n (.ofMul ζ) := by
  apply Subtype.ext
  simp only [AddSubgroupClass.coe_sub, coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap,
    coe_tateDivisionPoint, coe_tateRootsOfUnityHom]
  rw [map_tateUnitHom q hq σ hσ, hζ, ofMul_mul, map_add, add_sub_cancel_right,
    toMul_ofMul]

omit [CompleteSpace K] [IsUltrametricDist K] [CompleteSpace L] [IsUltrametricDist L]
  [DecidableEq L] in
include hq in
private theorem ne_zero_of_tateParameter_pow_eq (u : Lˣ)
    (hu : u ^ n = Units.map (algebraMap K L : K →* L) q) : n ≠ 0 := by
  intro hn
  have hnorm := congrArg (fun v : Lˣ ↦ ‖(v : L)‖) hu
  have hq1 : ‖(q : K)‖ = 1 := by simpa [hn] using hnorm.symm
  exact hq.ne hq1

/-- Two continuous coefficient maps agree on a division point exactly when they agree on
its chosen parameter root. -/
theorem torsionByMap_tateDivisionPoint_eq_iff
    {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
    [IsUltrametricDist M] [DecidableEq M]
    (σ τ : L →ₐ[K] M) (hσ : Continuous σ) (hτ : Continuous τ) (u : Lˣ)
    (hu : u ^ n = Units.map (algebraMap K L : K →* L) q) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap (tateDivisionPoint q hq n u hu) =
        torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap (tateDivisionPoint q hq n u hu) ↔
      Units.map (σ : L →* M) u = Units.map (τ : L →* M) u := by
  have hpow (ι : L →ₐ[K] M) :
      (Units.map (ι : L →* M) u) ^ n = Units.map (algebraMap K M : K →* M) q := by
    rw [← map_pow, hu]
    ext
    simp
  let ζ : rootsOfUnity n M := ⟨Units.map (σ : L →* M) u / Units.map (τ : L →* M) u, by
    rw [mem_rootsOfUnity, div_pow, hpow, hpow, div_self']⟩
  have hdiff : torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
        (tateDivisionPoint q hq n u hu) -
      torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap (tateDivisionPoint q hq n u hu) =
        tateRootsOfUnityHom M q hq n (.ofMul ζ) := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap,
      coe_tateDivisionPoint, coe_tateRootsOfUnityHom, toMul_ofMul, ζ, Subtype.coe_mk,
      map_tateUnitHom q hq σ hσ, map_tateUnitHom q hq τ hτ, ofMul_div, map_sub]
  rw [← sub_eq_zero, hdiff, ← map_zero (tateRootsOfUnityHom M q hq n),
    (tateRootsOfUnityHom_injective M q hq n
      (ne_zero_of_tateParameter_pow_eq q hq n u hu)).eq_iff]
  simp only [ofMul_eq_zero, ζ, Subgroup.mk_eq_one, div_eq_one]

omit [CompleteSpace L] [IsUltrametricDist L] in
private theorem torsionByMap_tateCurveAt_id :
    torsionByMap (n : ℤ)
      (Point.map (W' := (tateCurveAt q hq).toAffine) (AlgHom.id K L)).toIntLinearMap =
        LinearMap.id := by
  ext P
  simp only [coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap, LinearMap.id_apply]
  exact Point.map_id _

/-- The division point represented by an `n`-th root `u` of `q` is fixed exactly when `u` is
fixed. Thus nontrivial Kummer action gives nontrivial action on Tate torsion. -/
theorem torsionByMap_tateDivisionPoint_eq_self_iff
    (σ : L →ₐ[K] L) (hσ : Continuous σ) (u : Lˣ)
    (hu : u ^ n = Units.map (algebraMap K L : K →* L) q) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap
        (tateDivisionPoint q hq n u hu) = tateDivisionPoint q hq n u hu ↔
      Units.map (σ : L →* L) u = u := by
  simpa only [torsionByMap_tateCurveAt_id q hq n, LinearMap.id_apply, Units.ext_iff,
    Units.coe_map, AlgHom.coe_toMonoidHom, AlgHom.coe_id, id_eq] using
    torsionByMap_tateDivisionPoint_eq_iff q hq n σ (AlgHom.id K L) hσ continuous_id u hu

/-- If two coefficient maps agree on roots of unity, the difference of their actions
scales with the exponent: an exponent relation between `P` and `Q` gives the same relation
between their displacements. No parameter root need be chosen. -/
theorem torsionByMap_tateCurveAt_sub_eq_zsmul
    {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
    [IsUltrametricDist M] [DecidableEq M]
    (σ τ : L →ₐ[K] M) (hσ : Continuous σ) (hτ : Continuous τ)
    (hζ : ∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = restrictRootsOfUnity τ n ζ)
    (P Q : (((tateCurveAt q hq)⁄L).toAffine.Point)[(n : ℤ)])
    (a : ℤ) (ha : tateTorsionExponent L q hq n P = a • tateTorsionExponent L q hq n Q) :
    torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap P -
        torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap P =
      a • (torsionByMap (n : ℤ) (Point.map σ).toIntLinearMap Q -
        torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap Q) := by
  obtain ⟨ζ, rfl⟩ := exists_tateRootsOfUnityHom_add_zsmul L q hq n P Q a ha
  obtain ⟨ζ, rfl⟩ := Additive.ofMul.surjective ζ
  simp only [map_add, map_zsmul, torsionByMap_tateRootsOfUnityHom q hq n σ hσ,
    torsionByMap_tateRootsOfUnityHom q hq n τ hτ, hζ, smul_sub]
  abel

section ChosenRoot

variable (u : Lˣ) (hu : u ^ n = Units.map (algebraMap K L : K →* L) q)

include hu in
/-- Two continuous coefficient maps induce the same map on Tate `n`-torsion exactly when
they agree on the `n`-th roots of unity and a chosen `n`-th root of the parameter. -/
theorem torsionByMap_tateCurveAt_eq_iff
    {M : Type*} [NormedField M] [NormedAlgebra K M] [CompleteSpace M]
    [IsUltrametricDist M] [DecidableEq M]
    (σ τ : L →ₐ[K] M) (hσ : Continuous σ) (hτ : Continuous τ) :
    torsionByMap (n : ℤ) (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap =
        torsionByMap (n : ℤ) (Point.map τ).toIntLinearMap ↔
      (∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = restrictRootsOfUnity τ n ζ) ∧
        Units.map (σ : L →* M) u = Units.map (τ : L →* M) u := by
  have hn := ne_zero_of_tateParameter_pow_eq q hq n u hu
  constructor
  · intro h
    refine ⟨fun ζ ↦ ?_, ?_⟩
    · have he := LinearMap.congr_fun h (tateRootsOfUnityHom L q hq n (.ofMul ζ))
      rw [torsionByMap_tateRootsOfUnityHom q hq n σ hσ,
        torsionByMap_tateRootsOfUnityHom q hq n τ hτ] at he
      exact Additive.ofMul.injective ((tateRootsOfUnityHom_injective M q hq n hn) he)
    · exact (torsionByMap_tateDivisionPoint_eq_iff q hq n σ τ hσ hτ u hu).mp
        (LinearMap.congr_fun h _)
  · rintro ⟨hζ, huστ⟩
    apply LinearMap.ext
    intro P
    obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (tateTorsionExponent L q hq n P)
    rw [Ideal.Quotient.mk_eq_mk, eq_intCast] at ha
    have hdiv := (torsionByMap_tateDivisionPoint_eq_iff q hq n σ τ hσ hτ u hu).mpr huστ
    have h := torsionByMap_tateCurveAt_sub_eq_zsmul q hq n σ τ hσ hτ hζ P
      (tateDivisionPoint q hq n u hu) a (by simpa using ha.symm)
    simpa only [hdiv, sub_self, smul_zero, sub_eq_zero] using h

include hu in
/-- A continuous coefficient endomorphism fixes all Tate `n`-torsion exactly when it fixes
the roots of unity and a chosen `n`-th root of the parameter. This detects triviality of
the entire action, not only of its action on the exponent quotient. -/
theorem torsionByMap_tateCurveAt_eq_id_iff
    (σ : L →ₐ[K] L) (hσ : Continuous σ) :
    torsionByMap (n : ℤ) (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap =
        LinearMap.id ↔
      (∀ ζ : rootsOfUnity n L, restrictRootsOfUnity σ n ζ = ζ) ∧
        Units.map (σ : L →* L) u = u := by
  have hid : torsionByMap (n : ℤ)
      (Point.map (W' := (tateCurveAt q hq).toAffine) (AlgHom.id K L)).toIntLinearMap =
        LinearMap.id := torsionByMap_tateCurveAt_id q hq n
  have hidUnits (v : Lˣ) : Units.map (AlgHom.id K L : L →* L) v = v :=
    DFunLike.congr_fun (Units.map_id L) v
  have hidRoots (ζ : rootsOfUnity n L) : restrictRootsOfUnity (AlgHom.id K L) n ζ = ζ := by
    ext
    simp
  simpa only [hid, hidUnits, hidRoots] using
    torsionByMap_tateCurveAt_eq_iff q hq n u hu σ (AlgHom.id K L) hσ continuous_id

end ChosenRoot

/-- Fixing all `ℓ`-power roots of unity makes the action on the Tate module of a Tate curve
unipotent of index at most two. No basis, discreteness of the valuation, or algebraicity of the
complete extension is required. -/
theorem tateModuleGaloisRepresentation_tateCurveAt_sub_one_sq_eq_zero (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : L ≃ₐ[K] L) (hσ : Continuous σ)
    (hζ : ∀ k, ∀ ζ : rootsOfUnity (ℓ ^ k) L,
      restrictRootsOfUnity σ.toAlgHom (ℓ ^ k) ζ = ζ) :
    ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ - 1) ^ 2 = 0 :=
  (tateCurveAt q hq).tateModuleGaloisRepresentation_sub_one_sq_eq_zero σ fun k ↦
    torsionByMap_tateCurveAt_sub_id_sq_eq_zero q hq (ℓ ^ k) σ.toAlgHom hσ (hζ k)

end TauCeti
