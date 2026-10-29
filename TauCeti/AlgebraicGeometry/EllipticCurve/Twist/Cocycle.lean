/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import TauCeti.AlgebraicGeometry.EllipticCurve.Aut
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisDescent
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Galois
import TauCeti.GroupTheory.GroupAction.Stabilizer
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Nonabelian.Basic

/-!
# The Galois cocycle of a pointed twist

Let `V` and `W` be Weierstrass curves over `K`, and let `C` carry `V` to `W` over an
algebraic extension `L/K`. Then `σ ↦ C (σ C)⁻¹` is a continuous cocycle with values in
the discrete automorphism group of `W` over `L`. Its cohomology class does not depend
on `C`. Over a Galois extension, two such classes agree exactly when their source
curves are isomorphic over `K` by a change of variables. In particular, the class is
trivial exactly when `V` is isomorphic to `W` over `K`.

The construction applies in every characteristic, including over a separable closure of
an imperfect field. It does not assume ellipticity: the equation-level construction also
makes sense for singular Weierstrass cubics.

## Main results

* `WeierstrassCurve.VariableChange.twistCocycle`: the continuous cocycle of a trivialisation.
* `WeierstrassCurve.VariableChange.twistCohomologyClass_eq`: independence of the trivialisation.
* `WeierstrassCurve.VariableChange.twistCohomologyClass_eq_iff`: equality of classes detects
  isomorphism over the base field.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.2 and X.5.
* J.-P. Serre, *Galois Cohomology*, III.1.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti

variable {K : Type*} [Field K] (W : WeierstrassCurve K)
  (L : Type*) [Field L] [Algebra K L]

/-- The automorphisms of `W` over `L`, with the discrete topology imposed, as coefficients
for continuous nonabelian Galois cohomology. -/
def AutCoeff : Type _ := (W.baseChange L).autGroup

instance : Group (W.AutCoeff L) := inferInstanceAs (Group (W.baseChange L).autGroup)
instance : TopologicalSpace (W.AutCoeff L) := ⊥
instance : DiscreteTopology (W.AutCoeff L) := ⟨rfl⟩

/-- Identify the discrete coefficient group with the stabilizer of the base-changed equation. -/
def autCoeffEquiv : (W.baseChange L).autGroup ≃* W.AutCoeff L := MulEquiv.refl _

/-- Automorphism coefficients are determined by their underlying change of variables. -/
@[ext]
theorem AutCoeff.ext {a b : W.AutCoeff L}
    (h : ((W.autCoeffEquiv L).symm a).val = ((W.autCoeffEquiv L).symm b).val) : a = b :=
  (W.autCoeffEquiv L).symm.injective (Subtype.ext h)

variable {L}

instance : SMul Gal(L/K) (W.AutCoeff L) where
  smul σ a := W.autCoeffEquiv L
    ⟨(W.autCoeffEquiv L).symm a |>.val.map (σ : L →+* L),
      map_smul_baseChange_eq L σ.toAlgHom ((W.autCoeffEquiv L).symm a).property⟩

/-- Galois acts on the automorphism group by conjugating the four coefficients. -/
@[simp]
theorem autCoeffEquiv_symm_smul (σ : Gal(L/K)) (a : W.AutCoeff L) :
    ((W.autCoeffEquiv L).symm (σ • a)).val =
      ((W.autCoeffEquiv L).symm a).val.map (σ : L →+* L) := (rfl)

/-- Galois conjugation commutes with the identification of the automorphism coefficient group. -/
@[simp]
theorem smul_autCoeffEquiv (σ : Gal(L/K)) (a : (W.baseChange L).autGroup) :
    σ • W.autCoeffEquiv L a = W.autCoeffEquiv L
      ⟨a.val.map (σ : L →+* L), map_smul_baseChange_eq L σ.toAlgHom a.property⟩ := (rfl)

instance : MulDistribMulAction Gal(L/K) (W.AutCoeff L) where
  one_smul a := by
    apply AutCoeff.ext
    simp [AlgEquiv.aut_one]
  mul_smul σ τ a := by
    apply AutCoeff.ext
    simp [AlgEquiv.aut_mul, VariableChange.map_map]
  smul_one σ := by
    apply AutCoeff.ext
    simp
  smul_mul σ a b := by
    apply AutCoeff.ext
    simp

/-- Over an algebraic extension the discrete automorphism group has a continuous Galois
action: its orbit maps depend on only four algebraic coefficients. -/
instance AutCoeff.instContinuousSMul [Algebra.IsAlgebraic K L] :
    ContinuousSMul Gal(L/K) (W.AutCoeff L) := by
  refine continuousSMul_iff_stabilizer_isOpen.2 fun a ↦ ?_
  let C := ((W.autCoeffEquiv L).symm a).val
  have h := (C.isLocallyConstant_map_of_isAlgebraic (K := K)).isOpen_fiber C
  convert h using 1
  ext σ
  simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, Set.mem_ofPred_eq,
    AutCoeff.ext_iff, autCoeffEquiv_symm_smul, C]

namespace VariableChange

variable {W} {V : WeierstrassCurve K}

section Algebraic

variable [Algebra.IsAlgebraic K L] (C : VariableChange L) (hC : C • V.baseChange L = W.baseChange L)

/-- The continuous cocycle of a pointed trivialisation `C : V_L ≅ W_L`:
`σ ↦ C (σ C)⁻¹`. -/
def twistCocycle : NonabelianH1.Cocycle Gal(L/K) (W.AutCoeff L) where
  toFun σ := W.autCoeffEquiv L ⟨C * (C.map (σ : L →+* L))⁻¹,
    mul_inv_mem_stabilizer_of_smul_eq C (C.map (σ : L →+* L)) hC
      (map_smul_baseChange_eq L σ.toAlgHom hC)⟩
  continuous_toFun := by
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    convert ((C.isLocallyConstant_map_of_isAlgebraic (K := K)).comp
      (fun D ↦ C * D⁻¹)).isOpen_fiber (((W.autCoeffEquiv L).symm a).val) using 1
    ext σ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply,
      AutCoeff.ext_iff,
      MulEquiv.symm_apply_apply, Set.mem_ofPred_eq]
  map_mul' σ τ := by
    apply AutCoeff.ext
    simp only [_root_.map_mul, Subgroup.coe_mul, autCoeffEquiv_symm_smul,
      MulEquiv.symm_apply_apply, VariableChange.map_mul, VariableChange.map_inv,
      VariableChange.map_map]
    rw [AlgEquiv.aut_mul, AlgEquiv.toRingHom_trans]
    group

/-- The cocycle of a trivialisation, expressed in the automorphism coefficient group. -/
theorem twistCocycle_apply (σ : Gal(L/K)) :
    twistCocycle C hC σ = W.autCoeffEquiv L
      ⟨C * (C.map (σ : L →+* L))⁻¹,
        by
          exact mul_inv_mem_stabilizer_of_smul_eq C (C.map (σ : L →+* L)) hC
            (map_smul_baseChange_eq L σ.toAlgHom hC)⟩ := (rfl)

/-- The coefficient formula for the cocycle of a trivialisation. -/
@[simp]
theorem autCoeffEquiv_symm_twistCocycle (σ : Gal(L/K)) :
    ((W.autCoeffEquiv L).symm (twistCocycle C hC σ)).val =
      C * (C.map (σ : L →+* L))⁻¹ := (rfl)

/-- The nonabelian cohomology class associated to a pointed trivialisation. -/
def twistCohomologyClass : NonabelianH1 Gal(L/K) (W.AutCoeff L) :=
  NonabelianH1.mk (twistCocycle C hC)

/-- The class is represented by the cocycle `σ ↦ C (σ C)⁻¹`. -/
theorem twistCohomologyClass_def :
    twistCohomologyClass C hC = NonabelianH1.mk (twistCocycle C hC) := (rfl)

/-- Two trivialisations of the same pointed twist give the same cohomology class. -/
theorem twistCohomologyClass_eq (D : VariableChange L)
    (hD : D • V.baseChange L = W.baseChange L) :
    twistCohomologyClass C hC = twistCohomologyClass D hD := by
  rw [twistCohomologyClass_def, twistCohomologyClass_def]
  refine NonabelianH1.mk_eq_mk_iff.2
    ⟨W.autCoeffEquiv L ⟨C * D⁻¹, mul_inv_mem_stabilizer_of_smul_eq C D hC hD⟩,
      fun σ ↦ ?_⟩
  apply AutCoeff.ext
  simp only [_root_.map_mul, _root_.map_inv, Subgroup.coe_mul, Subgroup.coe_inv,
    autCoeffEquiv_symm_twistCocycle, autCoeffEquiv_symm_smul, MulEquiv.symm_apply_apply,
    VariableChange.map_mul, VariableChange.map_inv]
  group

/-- The identity trivialisation gives the trivial cocycle. -/
@[simp]
theorem twistCocycle_one :
    twistCocycle (W := W) (V := W) (1 : VariableChange L) (one_smul _ _) = 1 := by
  ext σ : 1
  apply AutCoeff.ext
  simp [autCoeffEquiv_symm_twistCocycle]

end Algebraic

section Galois

variable [IsGalois K L] (C : VariableChange L)
  (hC : C • V.baseChange L = W.baseChange L)

/-- Two pointed twists give the same Galois cohomology class exactly when they are
isomorphic by a change of variables over the base field. -/
theorem twistCohomologyClass_eq_iff {U : WeierstrassCurve K} (D : VariableChange L)
    (hD : D • U.baseChange L = W.baseChange L) :
    twistCohomologyClass C hC = twistCohomologyClass D hD ↔
      ∃ B : VariableChange K, B • V = U := by
  constructor
  · intro h
    rw [twistCohomologyClass_def, twistCohomologyClass_def,
      NonabelianH1.mk_eq_mk_iff] at h
    obtain ⟨a, ha⟩ := h
    let A := ((W.autCoeffEquiv L).symm a).val
    have hfix : ∀ σ : Gal(L/K), (D⁻¹ * A⁻¹ * C).map (σ : L →+* L) = D⁻¹ * A⁻¹ * C := by
      intro σ
      have hσ := congrArg (fun b ↦ ((W.autCoeffEquiv L).symm b).val) (ha σ)
      simp only [autCoeffEquiv_symm_twistCocycle, _root_.map_mul, _root_.map_inv,
        Subgroup.coe_mul, Subgroup.coe_inv, autCoeffEquiv_symm_smul] at hσ
      simp only [VariableChange.map_mul, VariableChange.map_inv]
      calc
        (D.map (σ : L →+* L))⁻¹ * (A.map (σ : L →+* L))⁻¹ * C.map (σ : L →+* L) =
            D⁻¹ * (D * (D.map (σ : L →+* L))⁻¹) *
              (A.map (σ : L →+* L))⁻¹ * C.map (σ : L →+* L) := by group
        _ = D⁻¹ * (A⁻¹ * (C * (C.map (σ : L →+* L))⁻¹) * A.map (σ : L →+* L)) *
              (A.map (σ : L →+* L))⁻¹ * C.map (σ : L →+* L) := by rw [hσ]
        _ = D⁻¹ * A⁻¹ * C := by group
    obtain ⟨B, hB⟩ := (mem_range_baseChange_iff_fixed (D⁻¹ * A⁻¹ * C)).2 hfix
    have hB' : B.baseChange L = D⁻¹ * A⁻¹ * C := hB
    refine ⟨B, smul_eq_of_baseChange_smul_eq (L := L) (algebraMap K L).injective B ?_⟩
    rw [hB', mul_smul, mul_smul, hC,
      inv_smul_eq_iff.mpr ((W.autCoeffEquiv L).symm a).property.symm,
      inv_smul_eq_iff.mpr hD.symm]
  · rintro ⟨B, hB⟩
    have hDB : (D * B.baseChange L) • V.baseChange L = W.baseChange L := by
      rw [mul_smul, baseChange_smul_baseChange, hB, hD]
    rw [twistCohomologyClass_eq C hC (D * B.baseChange L) hDB,
      twistCohomologyClass_def, twistCohomologyClass_def]
    congr 1
    ext σ : 1
    apply AutCoeff.ext
    have hBfix : (B.baseChange L).map (σ : L →+* L) = B.baseChange L := by
      simpa only [AlgEquiv.toAlgHom_toRingHom] using B.map_baseChange (σ : L →ₐ[K] L)
    rw [autCoeffEquiv_symm_twistCocycle, autCoeffEquiv_symm_twistCocycle,
      VariableChange.map_mul, hBfix]
    group

/-- A twist has trivial Galois cohomology class exactly when `V` is isomorphic to `W`
by a change of variables defined over the base field. -/
@[simp]
theorem twistCohomologyClass_eq_one_iff :
    twistCohomologyClass C hC = 1 ↔ ∃ B : VariableChange K, B • V = W := by
  simpa only [twistCohomologyClass_def, twistCocycle_one, NonabelianH1.mk_one] using
    twistCohomologyClass_eq_iff C hC (1 : VariableChange L) (one_smul _ _)

end Galois

end VariableChange

end WeierstrassCurve
