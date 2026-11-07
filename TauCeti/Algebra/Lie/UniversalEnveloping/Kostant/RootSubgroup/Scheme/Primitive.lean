/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.Algebra.Module.Primitive
import TauCeti.LinearAlgebra.SymmetricAlgebra.Basic

/-!
# Closed root subgroups detected by primitive strings

Let a nilpotent root operator preserve an integral lattice through all its divided powers.
If a lattice vector `m` satisfies `e² m = 0` and `e m` is primitive, its exponential defines a
closed immersion `𝔾ₐ → GLₙ` in **any** integral basis of the lattice. Neither `m` nor `e m`
has to be a member of that basis. This is useful for weight bases, which need not contain a
prescribed rank-one string.

An integral functional `ℓ` with `ℓ(e m) = 1` recovers the additive parameter from the regular
matrix coefficient `g ↦ ℓ(g m) - ℓ(m)`. Thus the root-subgroup coordinate map hits the generator
of the additive coordinate algebra. The basis-step criterion in
`TauCeti/Algebra/Lie/UniversalEnveloping/Kostant/RootSubgroup/Scheme/ClosedImmersion.lean`
is a special case, with the same represented subgroup and chosen coordinates.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory TensorProduct WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L ι κ : Type*} {V : Type}
variable [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (i : ι) (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

/-- **The generic matrix of a root subgroup is its matrix at the universal point of `𝔾ₐ`.** The
identity of the additive coordinate algebra is a point of `𝔾ₐ` over that algebra, and the
root-subgroup matrix there is the image of the generic matrix of `GL n` under the root-subgroup
coordinate morphism. A matrix formula proved at every algebra-valued point is read on the
coordinate morphism through this equation, which is the only place the universal point is
handled. -/
theorem map_genericMatrix_eq_kostantRootSubgroupMatrix :
    (GeneralLinear.genericMatrix ℤ n).map
        (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom =
      (kostantRootSubgroupMatrix e h ρ M hM i hnil b
        (toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)))).val := by
  let f := kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b
  have hpoint : GeneralLinear.pointToGeneralLinear n
      (toConv ((toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))).ofConv.comp
        f.hom.toAlgHom)) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        (toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))) :=
    pointsMulEquiv_kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b
      (AdditiveGroup.coordinateHopfAlgebra ℤ)
      (toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ)))
  have hpoint' : GeneralLinear.pointToGeneralLinear n (toConv f.hom.toAlgHom) =
      kostantRootSubgroupMatrix e h ρ M hM i hnil b
        (toConv (AlgHom.id ℤ (AdditiveGroup.coordinateHopfAlgebra ℤ))) := by
    simpa only [AlgHom.id_comp, WithConv.ofConv_toConv] using hpoint
  rw [GeneralLinear.map_genericMatrix_eq_coe_pointToGeneralLinear]
  simpa only [f] using congrArg
    (fun g : Matrix.GeneralLinearGroup (Fin n) (AdditiveGroup.coordinateHopfAlgebra ℤ) => g.1)
    hpoint'

local notation "op" => kostantRootOperator e h ρ M hM i

/-- On a two-step string, the universal root matrix sends `m` to `m + X • e m`,
read in the chosen lattice basis. The vector need not be a basis vector. -/
theorem map_genericMatrix_kostantRootSubgroupCoordinateMap_mulVec_repr_of_sq_eq_zero (m : M)
    (hsq : op (op m) = 0) :
    ((GeneralLinear.genericMatrix ℤ n).map
        (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom).mulVec
        (fun s => (b.repr m s : AdditiveGroup.coordinateHopfAlgebra ℤ)) =
      fun r => (b.repr m r : AdditiveGroup.coordinateHopfAlgebra ℤ) +
        SymmetricAlgebra.ι ℤ ℤ 1 * (b.repr (op m) r : AdditiveGroup.coordinateHopfAlgebra ℤ) := by
  classical
  let A := AdditiveGroup.coordinateHopfAlgebra ℤ
  let p := toConv (AlgHom.id ℤ A)
  have hsq' : (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) ^ 2 • (m : V) = 0 := by
    have hm := congrArg Subtype.val hsq
    simpa only [coe_kostantRootOperator_apply, ZeroMemClass.coe_zero, pow_two,
      Module.End.smul_def, mul_apply_eq_comp] using hm
  have haction : (kostantRootSubgroupPoints e h ρ M hM i hnil p).val (1 ⊗ₜ[ℤ] m) =
      1 ⊗ₜ[ℤ] m + (SymmetricAlgebra.ι ℤ ℤ 1) ⊗ₜ[ℤ] op m := by
    rw [kostantRootSubgroupPoints_val,
      baseChangeExp_tmul_of_pow_smul_eq_zero _ _ _ hnil _ _ _ hsq']
    have hfirst : integralDividedPower (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M 1
        (fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM i 1 hv) m =
        op m := by
      apply Subtype.ext
      rw [coe_integralDividedPower_one_apply, coe_kostantRootOperator_apply,
        Module.End.smul_def]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      mul_one, integralDividedPower_zero, one_apply_eq_self, hfirst,
      AdditiveGroup.toAdd_gaPointsMulEquiv, p]
    -- Evaluating the identity algebra homomorphism at the generator is definitionally itself.
    rfl
  rw [map_genericMatrix_eq_kostantRootSubgroupMatrix]
  -- The universal-point formula uses the category object's integral algebra structure,
  -- whereas matrix coordinates use the canonical one on the same symmetric algebra.
  erw [coe_kostantRootSubgroupMatrix e h ρ M hM i hnil b p]
  have hrepr : (fun s => (b.repr m s : A)) = ⇑((b.baseChange A).repr (1 ⊗ₜ[ℤ] m)) := by
    ext s
    simp only [Module.Basis.baseChange_repr_tmul, zsmul_eq_mul, mul_one]
  erw [hrepr, LinearMap.toMatrix_mulVec_repr, haction]
  ext r
  simp only [map_add, Finsupp.add_apply, Module.Basis.baseChange_repr_tmul,
    zsmul_eq_mul, mul_comm, one_mul]

/-- A primitive two-step string makes the root-subgroup coordinate map surjective.
An integral functional taking value one on `e m` detects the polynomial generator. -/
theorem kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive (m : M)
    (hsq : op (op m) = 0) (hprim : IsPrimitive (op m)) :
    Function.Surjective (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom := by
  classical
  obtain ⟨ℓ, hℓ⟩ := isPrimitive_def.mp hprim
  let C := GeneralLinear.coordinateHopfAlgebra ℤ n
  let f := (kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b).hom.toAlgHom
  let z : C := ∑ r, ℓ (b r) • ∑ s, b.repr m s • GeneralLinear.genericMatrix ℤ n r s
  have hz : f z = (ℓ m : AdditiveGroup.coordinateHopfAlgebra ℤ) +
      SymmetricAlgebra.ι ℤ ℤ 1 := by
    have hvec := map_genericMatrix_kostantRootSubgroupCoordinateMap_mulVec_repr_of_sq_eq_zero
      e h ρ M hM i hnil b m hsq
    have heval (v : M) : ∑ r, (ℓ (b r) : AdditiveGroup.coordinateHopfAlgebra ℤ) *
        b.repr v r = (ℓ v : AdditiveGroup.coordinateHopfAlgebra ℤ) := by
      have hv := congrArg (fun v : M => (ℓ v : AdditiveGroup.coordinateHopfAlgebra ℤ))
        (b.sum_repr v)
      simpa only [map_sum, map_zsmul, zsmul_eq_mul, Int.cast_id, Int.cast_sum,
        Int.cast_mul, mul_comm] using hv
    simp only [z, map_sum, map_zsmul]
    have hrow (r : Fin n) : ∑ s,
        (b.repr m s : AdditiveGroup.coordinateHopfAlgebra ℤ) *
          f (GeneralLinear.genericMatrix ℤ n r s) =
        (b.repr m r : AdditiveGroup.coordinateHopfAlgebra ℤ) +
          SymmetricAlgebra.ι ℤ ℤ 1 * b.repr (op m) r := by
      simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, f, zsmul_eq_mul, mul_comm]
        using congrFun hvec r
    simp only [zsmul_eq_mul, hrow, mul_add]
    rw [Finset.sum_add_distrib]
    rw [heval]
    congr 1
    calc
      _ = SymmetricAlgebra.ι ℤ ℤ 1 * ∑ r,
          (ℓ (b r) : AdditiveGroup.coordinateHopfAlgebra ℤ) * b.repr (op m) r := by
        rw [Finset.mul_sum]
        congr 1
        funext r
        ring
      _ = _ := by rw [heval, hℓ]; simp
  apply f.surjective_of_ι_one_mem_range
  refine ⟨z - algebraMap ℤ C (ℓ m), ?_⟩
  simp [map_sub, hz]

/-- The root morphism is a closed immersion whenever a primitive two-step lattice string
detects its parameter. This does not require adapting the lattice basis to the string. -/
theorem isClosedImmersion_kostantRootSubgroup_of_isPrimitive (m : M)
    (hsq : op (op m) = 0) (hprim : IsPrimitive (op m)) :
    IsClosedImmersion (kostantRootSubgroup e h ρ M hM i hnil b).hom.hom.left := by
  rw [kostantRootSubgroup_def]
  exact (CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
    (AdditiveGroup.groupScheme_def ℤ) (GeneralLinear.groupScheme_def ℤ n) _).2
    (kostantRootSubgroupCoordinateMap_surjective_of_isPrimitive e h ρ M hM i hnil b m hsq hprim)

end TauCeti.UniversalEnvelopingAlgebra
