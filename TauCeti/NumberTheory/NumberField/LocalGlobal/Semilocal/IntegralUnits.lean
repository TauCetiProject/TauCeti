/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.GaloisAction
public import TauCeti.NumberTheory.LocalField.UnitFiltration.GaloisAction
import Mathlib.Tactic.DSimpPercent

/-!
# Coinduction of semi-local integral units

For a finite Galois extension `L/K` and a finite place `v` of `K`, the subgroup of
`(K_v ⊗[K] L)ˣ` integral and invertible in every component is coinduced from `𝒪[L_w]ˣ`
for any place `w` above `v`. The decomposition group acts on that component through its
canonical action on `L_w`.

The subgroup is defined using the depth-zero unit filtrations in the actual completions.
Its coinduction isomorphism is the restriction of `TauCeti.semilocalUnitsCoindIso`.
This comparison lets Shapiro's lemma compute the integral factors outside a finite set
of places in the cohomology of ideles, rather than replacing those factors by `L_wˣ`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §2.
-/

public noncomputable section

open IsDedekindDomain NumberField CategoryTheory
open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField AdicCompletionExtension Pointwise TensorProduct WithZero

namespace TauCeti

universe u

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The units of `K_v ⊗[K] L` whose components belong to the integer-unit groups
of every completion above `v`. -/
def semilocalIntegralUnits (L : Type u) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (v.adicCompletion K ⊗[K] L)ˣ :=
  ⨅ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
    (unitFiltration (w.1.adicCompletion L) 0).comap
      (Units.map ((Pi.evalMonoidHom (fun w' :
        {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} ↦
          w'.1.adicCompletion L) w).comp (semilocalEquiv L v : _ →* _)))

/-- A semi-local unit is integral and invertible exactly when every component has valuation one. -/
@[simp]
theorem mem_semilocalIntegralUnits_iff (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletion K ⊗[K] L)ˣ) :
    y ∈ semilocalIntegralUnits L v ↔
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Valued.v (semilocalEquiv L v y w) = 1 := by
  simp only [semilocalIntegralUnits, Subgroup.mem_iInf, Subgroup.mem_comap,
    mem_unitFiltration_zero_adicCompletion_iff, Units.coe_map, MonoidHom.coe_comp,
    Function.comp_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_ofClass]

/-- The Galois action preserves the group of semi-local integral units. -/
theorem baseChangeAutHom_mem_semilocalIntegralUnits (v : HeightOneSpectrum (𝓞 K))
    (g : L ≃ₐ[K] L) {y : (v.adicCompletion K ⊗[K] L)ˣ}
    (hy : y ∈ semilocalIntegralUnits L v) :
    Units.map (Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L g : _ →* _) y ∈
      semilocalIntegralUnits L v := by
  rw [mem_semilocalIntegralUnits_iff] at hy ⊢
  intro w
  let w' := (liesOverEquivPrimesOver (𝓞 L) v).symm
    (g⁻¹ • liesOverEquivPrimesOver (𝓞 L) v w)
  have hw : w.1.asIdeal = g • w'.1.asIdeal := by
    simp [w', liesOverEquivPrimesOver_symm_apply,
      coe_smul_primesOver_ringOfIntegers, liesOverEquivPrimesOver_apply]
  rw [Units.coe_map, MonoidHom.coe_ofClass, semilocalEquiv_baseChangeAutHom g hw,
    valued_completionCongr]
  exact hy w'

/-- The Galois action on the group of semi-local integral units. -/
instance semilocalIntegralUnitsMulDistribMulAction (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction (L ≃ₐ[K] L) (semilocalIntegralUnits L v) := by
  letI := MulDistribMulAction.compHom (v.adicCompletion K ⊗[K] L)ˣ
    (Algebra.TensorProduct.baseChangeAutHom (K := K) (v.adicCompletion K) L)
  letI : SMul (L ≃ₐ[K] L) (semilocalIntegralUnits L v) :=
    ⟨fun g y ↦ ⟨Units.map
        (Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L g : _ →* _) y.1,
      baseChangeAutHom_mem_semilocalIntegralUnits v g y.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction (semilocalIntegralUnits L v).subtype
    fun _ _ ↦ rfl

/-- The restricted Galois action agrees with the action on the semi-local algebra. -/
@[simp]
theorem coe_smul_semilocalIntegralUnits (v : HeightOneSpectrum (𝓞 K))
    (g : L ≃ₐ[K] L) (y : semilocalIntegralUnits L v) :
    ((g • y : semilocalIntegralUnits L v) : (v.adicCompletion K ⊗[K] L)ˣ) =
      Units.map (Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L g : _ →* _) y.1 :=
  (rfl)

/-- The integral representation on the semi-local integer-unit group. -/
abbrev semilocalIntegralUnitsRep (L : Type u) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (semilocalIntegralUnits L v)

/-- Inclusion of the integral semi-local units in the full semi-local unit representation. -/
def semilocalIntegralUnitsIncl (L : Type u) [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) :
    semilocalIntegralUnitsRep L v ⟶ semilocalUnitsRep L v :=
  Rep.ofHom <| LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (semilocalIntegralUnits L v).subtype.toAdditive.toIntLinearMap fun g y ↦
      congrArg Additive.ofMul (coe_smul_semilocalIntegralUnits v g y.toMul)

/-- The semi-local representation inclusion evaluates to the subgroup inclusion. -/
-- Normalize the implicit restriction parameters so the simp rule matches after `Rep.res_obj_ρ`.
@[simp]
theorem semilocalIntegralUnitsIncl_apply (v : HeightOneSpectrum (𝓞 K))
    (y : Additive (semilocalIntegralUnits L v)) :
    dsimp% only [Rep.ofAlgebraAutOnUnits, Rep.res_obj_ρ]
      ((semilocalIntegralUnitsIncl L v).hom y = Additive.ofMul y.toMul.1) :=
  (rfl)

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The integer-unit group of `L_w`, with the action of its decomposition group. -/
abbrev decompositionIntegralUnitsRep : Rep ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
  Rep.res (decompositionHom v w)
    (Rep.ofMulDistribMulAction (w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L)
      (unitFiltration (w.adicCompletion L) 0))

private def integralUnitsComponentHom :
    semilocalIntegralUnits L v →* unitFiltration (w.adicCompletion L) 0 := by
  let c : (v.adicCompletion K ⊗[K] L)ˣ →* (w.adicCompletion L)ˣ :=
    Units.map ((Pi.evalMonoidHom (fun w' :
      {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} ↦
        w'.1.adicCompletion L) ⟨w, ‹_›⟩).comp (semilocalEquiv L v : _ →* _))
  refine (c.comp (semilocalIntegralUnits L v).subtype).codRestrict _ fun y ↦ ?_
  rw [mem_unitFiltration_zero_adicCompletion_iff]
  -- Evaluate the composed units map and the evaluation hom; the membership criterion
  -- then applies to exactly the chosen coordinate, without unfolding the subgroup.
  change Valued.v (semilocalEquiv L v y.1 ⟨w, ‹_›⟩) = 1
  exact (mem_semilocalIntegralUnits_iff v y.1).1 y.2 ⟨w, ‹_›⟩

/-- Projection to the chosen integral component, equivariant for its decomposition group. -/
private def integralUnitsComponent :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
      (semilocalIntegralUnitsRep L v) ⟶ decompositionIntegralUnitsRep v w := by
  refine Rep.ofHom ⟨(integralUnitsComponentHom v w).toAdditive.toIntLinearMap,
    fun d ↦ LinearMap.ext fun y ↦ ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact (semilocalEquiv_baseChangeAutHom (w := ⟨w, ‹_›⟩) (w' := ⟨w, ‹_›⟩)
    (d : L ≃ₐ[K] L) (MulAction.mem_stabilizer_iff.mp d.2).symm _).trans
      (DFunLike.congr_fun (decompositionHom_apply d) _).symm

/-- The coinduction map sends an integral semi-local unit `y` to the function
`g ↦ ((id ⊗ g)y)_w`, now valued in the integer-unit group of `L_w`. -/
def semilocalIntegralUnitsToCoind :
    semilocalIntegralUnitsRep L v ⟶
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
        (decompositionIntegralUnitsRep v w) :=
  Rep.resCoindToHom _ _ _ (integralUnitsComponent v w)

/-- The coinduction map evaluated at an automorphism is its component at `w`. -/
theorem semilocalIntegralUnitsToCoind_apply (y : semilocalIntegralUnits L v)
    (g : L ≃ₐ[K] L) :
    (((((semilocalIntegralUnitsToCoind v w).hom (Additive.ofMul y)).1 g).toMul.1 :
      (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        semilocalEquiv L v (Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L g y.1)
          ⟨w, ‹_›⟩ :=
  (rfl)

/-- Coinduction of the inclusion of local integer units into the full local unit group. -/
def integralUnitsCoindIncl :
    Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
      (decompositionIntegralUnitsRep v w) ⟶
    Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
      (decompositionUnitsRep v w) :=
  Rep.coindMap _ ((Rep.resFunctor (decompositionHom v w)).map
    (unitFiltrationZeroIncl (v.adicCompletion K) (w.adicCompletion L)))

/-- The coinduced inclusion applies the local subgroup inclusion at each automorphism. -/
-- Normalize the implicit restriction parameters so the simp rule matches after `Rep.res_obj_ρ`.
@[simp]
theorem integralUnitsCoindIncl_apply
    (F : Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
      (decompositionIntegralUnitsRep v w)) (g : L ≃ₐ[K] L) :
    dsimp% only [Rep.ofAlgebraAutOnUnits, Rep.res_obj_ρ]
      (((integralUnitsCoindIncl v w).hom F).1 g = Additive.ofMul (F.1 g).toMul.1) := by
  simp only [integralUnitsCoindIncl, Rep.coindMap, Rep.hom_ofHom]
  exact unitFiltrationZeroIncl_apply _ _ _

private theorem integralUnitsCoindIncl_injective :
    Function.Injective (integralUnitsCoindIncl v w).hom := by
  intro x y h
  apply Subtype.ext
  funext g
  apply Additive.toMul.injective
  apply Subtype.ext
  have hh := congrArg (fun F ↦ Additive.toMul (α := (w.adicCompletion L)ˣ) (F.1 g)) h
  exact (congrArg (Additive.toMul (α := (w.adicCompletion L)ˣ))
    (integralUnitsCoindIncl_apply v w x g)).symm.trans
      (hh.trans (congrArg (Additive.toMul (α := (w.adicCompletion L)ˣ))
        (integralUnitsCoindIncl_apply v w y g)))

private theorem integralUnitsToCoind_incl (y : semilocalIntegralUnits L v) :
    (integralUnitsCoindIncl v w).hom
      ((semilocalIntegralUnitsToCoind v w).hom (Additive.ofMul y)) =
        (semilocalUnitsToCoind v w).hom (Additive.ofMul y.1) := by
  apply Subtype.ext
  funext g
  refine (integralUnitsCoindIncl_apply v w _ g).trans ?_
  apply Additive.toMul.injective
  apply Units.ext
  exact (semilocalIntegralUnitsToCoind_apply v w y g).trans
    (semilocalUnitsToCoind_apply v w y.1 g).symm

/-- Integral coinduction is the restriction of full coinduction: the canonical inclusion
square commutes as a square of Galois representations. -/
theorem semilocalIntegralUnitsToCoind_comp_incl :
    semilocalIntegralUnitsToCoind v w ≫ integralUnitsCoindIncl v w =
      semilocalIntegralUnitsIncl L v ≫ semilocalUnitsToCoind v w := by
  refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun y ↦ ?_))
  exact integralUnitsToCoind_incl v w y.toMul

private theorem semilocalIntegralUnitsToCoind_bijective [IsGalois K L] :
    Function.Bijective (semilocalIntegralUnitsToCoind v w).hom := by
  have hb : Function.Bijective (semilocalUnitsToCoind v w).hom := by
    have h := (Representation.equivOfIso (semilocalUnitsCoindIso v w)).toLinearEquiv.bijective
    -- `equivOfIso` uses the isomorphism's underlying intertwining map. Restate that
    -- coercion explicitly so the public `semilocalUnitsCoindIso_hom` lemma can rewrite it.
    change Function.Bijective (semilocalUnitsCoindIso v w).hom.hom at h
    rwa [semilocalUnitsCoindIso_hom] at h
  constructor
  · intro x y h
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Additive.ofMul.injective
    apply hb.injective
    exact (integralUnitsToCoind_incl v w x.toMul).symm.trans
      ((congrArg (integralUnitsCoindIncl v w).hom h).trans
        (integralUnitsToCoind_incl v w y.toMul))
  · intro F
    obtain ⟨y, hy⟩ := hb.surjective ((integralUnitsCoindIncl v w).hom F)
    -- Reuse surjectivity on all semi-local units. Transitivity on the places and
    -- preservation of valuation by completion transport force the preimage to be integral.
    obtain ⟨u, rfl⟩ : ∃ u : (v.adicCompletion K ⊗[K] L)ˣ, Additive.ofMul u = y :=
      ⟨Additive.toMul (α := (v.adicCompletion K ⊗[K] L)ˣ) y, rfl⟩
    have hint : u ∈ semilocalIntegralUnits L v := by
      rw [mem_semilocalIntegralUnits_iff]
      intro w'
      let := w'.2
      obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal
        w'.1.asIdeal w.asIdeal (L ≃ₐ[K] L)
      have hv : Valued.v (semilocalEquiv L v
          (Algebra.TensorProduct.baseChangeAutHom (v.adicCompletion K) L g u) ⟨w, ‹_›⟩) = 1 := by
        rw [← semilocalUnitsToCoind_apply v w u g]
        let val : Additive (w.adicCompletion L)ˣ → ℤᵐ⁰ := fun x ↦ Valued.v (x.toMul :
          w.adicCompletion L)
        have heq := congrArg (fun H ↦ val (H.1 g)) hy
        exact heq.trans ((congrArg val (integralUnitsCoindIncl_apply v w F g)).trans
          ((mem_unitFiltration_zero_adicCompletion_iff w).1 (F.1 g).toMul.2))
      rwa [semilocalEquiv_baseChangeAutHom g hg.symm, valued_completionCongr] at hv
    refine ⟨Additive.ofMul ⟨u, hint⟩, integralUnitsCoindIncl_injective v w ?_⟩
    exact (integralUnitsToCoind_incl v w ⟨u, hint⟩).trans hy

/-- **Semi-local integral units are coinduced from local integral units.** For a Galois
extension, projection to one completion identifies the representation on all integral
semi-local units with coinduction from the decomposition group of that completion. -/
def semilocalIntegralUnitsCoindIso [IsGalois K L] :
    semilocalIntegralUnitsRep L v ≅
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype
        (decompositionIntegralUnitsRep v w) :=
  Rep.mkIso ((semilocalIntegralUnitsToCoind v w).hom.ofBijective
    (semilocalIntegralUnitsToCoind_bijective v w))

/-- The coinduction isomorphism is the map obtained by projection to `w`. -/
@[simp]
theorem semilocalIntegralUnitsCoindIso_hom [IsGalois K L] :
    (semilocalIntegralUnitsCoindIso v w).hom = semilocalIntegralUnitsToCoind v w :=
  (rfl)

end TauCeti
