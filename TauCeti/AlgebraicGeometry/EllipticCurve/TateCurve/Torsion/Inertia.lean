/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Torsion.Galois
public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.NumberTheory.LocalField.RootsOfUnity.AlgebraicClosure
import TauCeti.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.Topology.Algebra.UniformRing

/-!
# Arithmetic inertia acts unipotently on Tate-curve torsion

For a Tate curve over a nonarchimedean local field `K`, every element of arithmetic inertia
satisfies `(σ - 1)² = 0` on torsion of order prime to the residue characteristic, and on the
corresponding Tate modules over the algebraic closure.

More generally, an endomorphism of an algebraic extension that contains and fixes a primitive
`m`-th root of unity acts with square-zero displacement on `m`-torsion. The spectral norm makes
the endomorphism continuous; the image of the primitive root generates the `m`-th roots of unity
in the completion as well. Injectivity of the point map descends the uniformization identity.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, V.3 and V.6.
* J.-P. Serre, *Local Fields*, Chapter II, §2 and Chapter III, §5.
-/

public noncomputable section

open UniformSpace ValuativeRel WeierstrassCurve WeierstrassCurve.Affine
open scoped AddSubgroup

namespace TauCeti

section AlgebraicExtension

variable {K L : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [DecidableEq L]
  (q : Kˣ) (hq : ‖(q : K)‖ < 1)

/-- An endomorphism of an algebraic extension fixing a primitive `m`-th root of unity acts
with square-zero displacement on the `m`-torsion of a Tate curve over that extension. -/
theorem torsionByMap_tateCurveAt_sub_id_sq_eq_zero_of_isAlgebraic {m : ℕ} [NeZero m]
    (σ : L →ₐ[K] L) {η : L} (hη : IsPrimitiveRoot η m) (hfix : σ η = η) :
    (torsionByMap (m : ℤ) (Point.map (W' := (tateCurveAt q hq).toAffine) σ).toIntLinearMap -
      LinearMap.id) ^ 2 = 0 := by
  classical
  let : NontriviallyNormedField K := .ofNormNeOne ⟨(q : K), q.ne_zero, hq.ne⟩
  let : NormedField L := spectralNorm.normedField K L
  let : NormedAlgebra K L := spectralNorm.normedAlgebra K L
  let C := Completion L
  let : IsUltrametricDist C := .of_normedAlgebra K
  let ι := IsScalarTower.toAlgHom K L C
  have hι (x : L) : ι x = (x : C) := by
    rw [IsScalarTower.coe_toAlgHom', Completion.algebraMap_def, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hσ : Continuous σ := (AddMonoidHomClass.isometry_of_norm σ fun x ↦ by
    simp only [NormedAlgebra.norm_eq_spectralNorm K, σ.spectralNorm_map]).continuous
  let τ : C →ₐ[K] C := Completion.mapAlgHom σ hσ
  have hτ : Continuous τ := Completion.continuous_mapAlgHom σ hσ
  have hcoe (x : L) : τ (x : C) = (σ x : C) := Completion.mapAlgHom_coe σ hσ x
  have hηC : IsPrimitiveRoot (η : C) m :=
    hη.map_of_injective (f := Completion.coeRingHom) (RingHom.injective _)
  have hroots (ζ : rootsOfUnity m C) : restrictRootsOfUnity τ m ζ = ζ := by
    apply Subtype.ext
    apply Units.ext
    simpa only [restrictRootsOfUnity_coe_apply, pow_one] using
      hηC.map_eq_pow (j := 1) τ (by rw [hcoe, hfix, pow_one])
      ((mem_rootsOfUnity' m (ζ : Cˣ)).mp ζ.property)
  have heq : τ.comp ι = ι.comp σ := by
    ext x
    simp only [AlgHom.comp_apply, hι, hcoe]
  have hcomm (P : ((tateCurveAt q hq)⁄L).toAffine.Point) :
      Point.map τ (Point.map ι P) = Point.map ι (Point.map σ P) := by
    rw [Point.map_map, Point.map_map, heq]
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  apply Point.map_injective (f := ι)
  have h := congrArg Subtype.val <| LinearMap.congr_fun
    (torsionByMap_tateCurveAt_sub_id_sq_eq_zero q hq m τ hτ hroots)
    (torsionByMap (m : ℤ) (Point.map ι).toIntLinearMap P)
  -- Evaluate both displacement operators on points, then commute the coefficient maps.
  simp only [pow_two, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.id_apply,
    AddSubgroupClass.coe_sub, coe_torsionByMap_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearMap.zero_apply, ZeroMemClass.coe_zero] at h ⊢
  simpa only [map_sub (Point.map ι), ← hcomm, map_zero] using h

/-- An automorphism of an algebraic extension that fixes a primitive root at every `ℓ`-power
level acts with square-zero displacement on the `ℓ`-adic Tate module of a Tate curve. -/
theorem tateModuleGaloisRepresentation_tateCurveAt_sub_one_sq_eq_zero_of_isAlgebraic
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : L ≃ₐ[K] L)
    (hζ : ∀ n : ℕ, ∃ η : L, IsPrimitiveRoot η (ℓ ^ n) ∧ σ η = η) :
    ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ - 1) ^ 2 = 0 := by
  apply (tateCurveAt q hq).tateModuleGaloisRepresentation_sub_one_sq_eq_zero σ
  intro n
  let : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨η, hη, hfix⟩ := hζ n
  exact torsionByMap_tateCurveAt_sub_id_sq_eq_zero_of_isAlgebraic q hq σ.toAlgHom hη hfix

end AlgebraicExtension

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [DecidableEq (AlgebraicClosure K)]
  (q : Kˣ) (hq : ‖(q : K)‖ < 1)

/-- Arithmetic inertia has square-zero displacement on the prime-to-residue-characteristic
`m`-torsion of a Tate curve over the algebraic closure. -/
theorem torsionByMap_tateCurveAt_sub_id_sq_eq_zero_of_mem_inertiaSubgroup {m : ℕ}
    (hm : m.Coprime (ringChar 𝓀[K])) {σ : Gal(AlgebraicClosure K/K)}
    (hσ : σ ∈ inertiaSubgroup K) :
    (torsionByMap (m : ℤ)
      (Point.map (W' := (tateCurveAt q hq).toAffine) σ.toAlgHom).toIntLinearMap -
        LinearMap.id) ^ 2 = 0 := by
  let : NeZero m := ⟨ne_zero_of_coprime_ringChar hm⟩
  let := hasEnoughRootsOfUnity_algebraicClosure_of_coprime_ringChar K hm
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) m
  exact torsionByMap_tateCurveAt_sub_id_sq_eq_zero_of_isAlgebraic q hq σ.toAlgHom hη
    (apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ hm hη.pow_eq_one)

/-- Arithmetic inertia acts unipotently of index at most two on the prime-to-residue-
characteristic Tate module of a Tate curve over the algebraic closure. -/
theorem tateModuleGaloisRepresentation_tateCurveAt_sub_one_sq_eq_zero_of_mem_inertiaSubgroup
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ.Coprime (ringChar 𝓀[K]))
    {σ : Gal(AlgebraicClosure K/K)} (hσ : σ ∈ inertiaSubgroup K) :
    ((tateCurveAt q hq).tateModuleGaloisRepresentation ℓ σ - 1) ^ 2 = 0 := by
  apply tateModuleGaloisRepresentation_tateCurveAt_sub_one_sq_eq_zero_of_isAlgebraic
  intro n
  let := hasEnoughRootsOfUnity_algebraicClosure_of_coprime_ringChar K (hℓ.pow_left n)
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure K) (ℓ ^ n)
  exact ⟨η, hη, apply_eq_self_of_mem_inertiaSubgroup_of_pow_eq_one hσ (hℓ.pow_left n) hη.pow_eq_one⟩

end TauCeti
