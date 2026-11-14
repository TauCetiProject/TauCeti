/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# Extensions of completed function fields

If `P'` lies over `P` in an algebraic extension `F' / F`, the embedding of fields extends
uniquely to a continuous ring homomorphism `P.Completion →+* P'.Completion`. The
extended valuation is the original completed valuation raised to the ramification index.
The induced algebra structure makes the completed extension available for local Galois theory.

The algebra structure is explicit, since choosing different places above `P` gives different
completed extensions. Install `completionExtensionAlgebra` locally. When the constant fields
agree, `isScalarTower_completionExtensionAlgebra` also identifies the original constant action
through the completed extension. The completed extension restricts to a local homomorphism
`completionIntegersExtension` of completed valuation rings, whose algebra
`completionIntegersExtensionAlgebra` is likewise installed locally.
No finiteness, separability, or residue-field assumptions are needed.

The construction uses Mathlib's `UniformSpace.Completion.mapRingHom`. The valuation-extension
argument follows `IsDedekindDomain.HeightOneSpectrum.valued_adicCompletionExtension` in
`TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean`, applied directly to the
intrinsic place completions rather than to an affine Dedekind model. That construction credits
Michael Stoll's EllipticCurves project and the FLT completion work of Kevin Buzzard, Andrew Yang
and Matthew Jasper.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections I.7 and III.1.
* J.-P. Serre, *Local Fields*, Chapter II, Section 3.
-/

public section

open UniformSpace Topology
open scoped WithZero

namespace TauCeti.Place

section Extension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)

include hP in
open WithZeroTopology in
private theorem uniformContinuous_withValExtension :
    UniformContinuous (WithVal.map P.valuation P'.valuation (algebraMap F F')) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hc : Continuous (Valued.v : Valuation (WithVal P.valuation) ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective fun γ ↦ by
      obtain ⟨x, hx⟩ := P.valuation_surjective γ
      exact ⟨WithVal.toVal P.valuation x, hx⟩
  have hcont := hc.pow (ramificationIdx F P')
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 :=
    (map_ne_zero_iff _ MonoidWithZeroHom.ValueGroup₀.embedding_injective).mpr γ.ne_zero
  filter_upwards [hcont.continuousAt.preimage_mem_nhds <| by
    simpa [(ramificationIdx_pos F P').ne'] using Iio_mem_nhds_zero hγ] with x hx
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa only [WithVal.map_apply, WithVal.valued_toVal,
    valuation_algebraMap_restrict k F P', hP, WithVal.apply_ofVal,
    Set.mem_preimage, Set.mem_Iio, Pi.pow_apply] using hx

/-- The unique continuous extension of `F → F'` to the completions at places with `P' ∣ P`. -/
noncomputable def completionExtension : P.Completion →+* P'.Completion :=
  UniformSpace.Completion.mapRingHom
    (WithVal.map P.valuation P'.valuation (algebraMap F F'))
    (uniformContinuous_withValExtension P P' hP).continuous

/-- The map of completions agrees with the original field embedding. -/
@[simp]
theorem completionExtension_completionEmbedding (x : F) :
    P.completionExtension P' hP (P.completionEmbedding x) =
      P'.completionEmbedding (algebraMap F F' x) := by
  simpa only [completionExtension, completionEmbedding_apply,
    WithVal.map_apply, WithVal.ofVal_toVal] using
    UniformSpace.Completion.mapRingHom_coe
      (uniformContinuous_withValExtension P P' hP).continuous (WithVal.toVal P.valuation x)

/-- The embedding of completions is continuous for the valuation topologies. -/
theorem continuous_completionExtension : Continuous (P.completionExtension P' hP) :=
  UniformSpace.Completion.continuous_map

/-- A continuous homomorphism of completed fields is determined by its values on `F`. -/
theorem eq_completionExtension_of_continuous {f : P.Completion →+* P'.Completion}
    (hf : Continuous f)
    (he : ∀ x : F, f (P.completionEmbedding x) =
      P'.completionEmbedding (algebraMap F F' x)) :
    f = P.completionExtension P' hP := by
  apply DFunLike.coe_injective
  exact P.denseRange_completionEmbedding.equalizer hf
    (P.continuous_completionExtension P' hP) (funext fun x ↦ by simp [he])

open WithZeroTopology in
/-- The valuation of the completed extension is scaled by the original ramification index. -/
@[simp]
theorem valuation_completionExtension (x : P.Completion) :
    Valued.v (P.completionExtension P' hP x) = Valued.v x ^ ramificationIdx F P' := by
  have hc : Continuous (Valued.v : Valuation P.Completion ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective (by
      intro γ
      obtain ⟨y, hy⟩ := P.completionPlace.valuation_surjective γ
      exact ⟨y, (P.completionPlace_valuation y).symm.trans hy⟩)
  have hc' : Continuous (Valued.v : Valuation P'.Completion ℤᵐ⁰) :=
    Valued.continuous_valuation_of_surjective (by
      intro γ
      obtain ⟨y, hy⟩ := P'.completionPlace.valuation_surjective γ
      exact ⟨y, (P'.completionPlace_valuation y).symm.trans hy⟩)
  apply congrFun <| P.denseRange_completionEmbedding.equalizer
    (hc'.comp (P.continuous_completionExtension P' hP)) (hc.pow _) ?_
  funext y
  simp [valuation_algebraMap_restrict k F P', hP]

/-- Completion preserves the ramification scaling of additive orders, including at zero. -/
@[simp]
theorem ord_completionExtension (x : P.Completion) :
    P'.completionPlace.ord (P.completionExtension P' hP x) =
      ramificationIdx F P' * P.completionPlace.ord x := by
  simp only [ord_def, completionPlace_valuation, valuation_completionExtension,
    WithZero.log_pow, Int.nsmul_eq_mul, mul_neg]

/-- The completed upper field is an algebra over the completed lower field. This explicit
structure must be installed locally with the chosen proof that `P'` lies over `P`. -/
@[instance_reducible]
noncomputable def completionExtensionAlgebra : Algebra P.Completion P'.Completion :=
  (P.completionExtension P' hP).toAlgebra

/-- The chosen completed-extension algebra map is the canonical continuous embedding. -/
theorem algebraMap_completionExtensionAlgebra :
    letI := P.completionExtensionAlgebra P' hP
    algebraMap P.Completion P'.Completion = P.completionExtension P' hP :=
  RingHom.algebraMap_toAlgebra _

/-- The extended embedding respects the original embeddings of the constant fields. -/
theorem completionExtension_algebraMap (c : k) :
    P.completionExtension P' hP (algebraMap k P.Completion c) =
      algebraMap k' P'.Completion (algebraMap k k' c) := by
  rw [← P.completionEmbedding.commutes c,
    completionExtension_completionEmbedding, ← IsScalarTower.algebraMap_apply k F F',
    IsScalarTower.algebraMap_apply k k' F', P'.completionEmbedding.commutes]

section Integers

/-- The completed extension carries the completed valuation ring of `P` into that of `P'`. -/
theorem completionExtension_mem_integers {x : P.Completion}
    (hx : x ∈ P.completionPlace.integers) :
    P.completionExtension P' hP x ∈ P'.completionPlace.integers := by
  rw [mem_integers_iff, completionPlace_valuation, valuation_completionExtension]
  exact pow_le_one' (by simpa using P.completionPlace.mem_integers_iff.mp hx) _

/-- The map of completed valuation rings induced by the completed extension. -/
noncomputable def completionIntegersExtension :
    P.completionPlace.integers →+* P'.completionPlace.integers :=
  (P.completionExtension P' hP).restrict _ _ fun _ hx ↦
    P.completionExtension_mem_integers P' hP hx

@[simp]
theorem coe_completionIntegersExtension (x : P.completionPlace.integers) :
    (P.completionIntegersExtension P' hP x : P'.Completion) = P.completionExtension P' hP x :=
  (rfl)

/-- Completing the valuation-ring embedding agrees with first completing both rings
and then applying the completed extension. -/
@[simp]
theorem completionIntegersExtension_completionIntegersEmbedding
    (x : (P'.restrict k F).integers) :
    (P'.restrict k F).completionIntegersExtension P' rfl
        ((P'.restrict k F).completionIntegersEmbedding x) =
      P'.completionIntegersEmbedding
        (algebraMap (P'.restrict k F).integers P'.integers x) := by
  apply Subtype.ext
  simp only [coe_completionIntegersExtension, completionIntegersEmbedding_apply,
    completionExtension_completionEmbedding, coe_algebraMap_integers]

/-- The map of completed valuation rings is local. -/
instance isLocalHom_completionIntegersExtension :
    IsLocalHom (P.completionIntegersExtension P' hP) where
  map_nonunit x hx := by
    rw [P.completionPlace.isUnit_iff_valuation_eq_one, completionPlace_valuation]
    rw [P'.completionPlace.isUnit_iff_valuation_eq_one, coe_completionIntegersExtension,
      completionPlace_valuation, valuation_completionExtension] at hx
    exact (pow_eq_one_iff_left (ramificationIdx_pos F P').ne').mp hx

/-- The completed valuation ring of `P'` is an algebra over the completed valuation ring of `P`.
Like `TauCeti.Place.completionExtensionAlgebra`, this structure depends on the chosen place over
`P` and is installed locally. -/
@[instance_reducible]
noncomputable def completionIntegersExtensionAlgebra :
    Algebra P.completionPlace.integers P'.completionPlace.integers :=
  (P.completionIntegersExtension P' hP).toAlgebra

/-- The chosen algebra map of completed valuation rings is `completionIntegersExtension`. -/
theorem algebraMap_completionIntegersExtensionAlgebra :
    letI := P.completionIntegersExtensionAlgebra P' hP
    algebraMap P.completionPlace.integers P'.completionPlace.integers =
      P.completionIntegersExtension P' hP :=
  RingHom.algebraMap_toAlgebra _

/-- The algebra map of the chosen completed valuation-ring extension is local, so
it induces the canonical extension of completed residue fields. -/
instance isLocalHom_algebraMap_completionIntegersExtensionAlgebra :
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsLocalHom (algebraMap P.completionPlace.integers P'.completionPlace.integers) := by
  rw [algebraMap_completionIntegersExtensionAlgebra]
  infer_instance

/-- The chosen algebra map of completed valuation rings is the completed extension. -/
theorem coe_algebraMap_completionIntegersExtensionAlgebra (x : P.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (algebraMap P.completionPlace.integers P'.completionPlace.integers x : P'.Completion) =
      P.completionExtension P' hP x :=
  (rfl)

/-- The action of `𝒪̂_P` on `F̂'_{P'}` via `F̂_P` factors through `𝒪̂_{P'}`. -/
theorem isScalarTower_completionIntegersExtension :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  let := P.completionIntegersExtensionAlgebra P' hP
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    P.algebraMap_completionExtensionAlgebra P' hP]
  exact (P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP x).symm

/-- The completed valuation ring above is torsion-free over the completed valuation ring below. -/
theorem isTorsionFree_completionIntegersExtension :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let := P.completionIntegersExtensionAlgebra P' hP
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h ↦ Subtype.ext ?_
  exact (P.completionExtension P' hP).injective <| by
    simpa only [P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP] using
      congrArg (fun z : P'.completionPlace.integers ↦ (z : P'.Completion)) h

/-- Completion preserves the ramification index of `P'` over `P`. -/
@[simp]
theorem ramificationIdx_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    ramificationIdx P.Completion P'.completionPlace = ramificationIdx F P' := by
  let := P.completionExtensionAlgebra P' hP
  rw [ramificationIdx_def,
    Valuation.ordIndex_eq_mul_of_forall_ord_eq _ P.completionPlace.valuation
      (e := ramificationIdx F P') fun x ↦ by
        simpa only [Valuation.ord_comap, ← ord_valuation,
          P.algebraMap_completionExtensionAlgebra P' hP] using P.ord_completionExtension P' hP x,
    Valuation.ordIndex_eq_one_of_surjective _ P.completionPlace.valuation_surjective, mul_one]

section IntegralClosureMap

include hP
attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- Every element of `F'` integral over `𝒪_P` maps into the completed valuation ring `𝒪̂_{P'}` for
every place `P'` lying over `P`. -/
theorem completionEmbedding_mem_integers_of_mem_integralClosure {x : F'}
    (hx : x ∈ integralClosure P.integers F') :
    P'.completionEmbedding x ∈ P'.completionPlace.integers := by
  have hx' : x ∈ P'.integers := P'.mem_integers_of_isIntegral
    (fun a ↦ by
      subst hP
      exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2) hx
  simpa only [mem_integers_iff, completionPlace_valuation, valuation_completionEmbedding] using hx'

/-- The canonical ring homomorphism from the integral closure `𝒪'_P` of `𝒪_P` in `F'` into the
completed valuation ring `𝒪̂_{P'}` at a place `P'` lying over `P`. -/
noncomputable def integralClosureToCompletionIntegers :
    integralClosure P.integers F' →+* P'.completionPlace.integers :=
  (P'.completionEmbedding.toRingHom.comp
    (Subalgebra.val (integralClosure P.integers F'))).codRestrict P'.completionPlace.integers
    fun x ↦ P.completionEmbedding_mem_integers_of_mem_integralClosure P' hP x.2

@[simp]
theorem coe_integralClosureToCompletionIntegers (x : integralClosure P.integers F') :
    (P.integralClosureToCompletionIntegers P' hP x : P'.Completion) =
      P'.completionEmbedding x :=
  (rfl)

@[simp]
theorem integralClosureToCompletionIntegers_algebraMap (r : P.integers) :
    P.integralClosureToCompletionIntegers P' hP
        (algebraMap P.integers (integralClosure P.integers F') r) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding r) := by
  apply Subtype.ext
  rw [coe_integralClosureToCompletionIntegers, coe_completionIntegersExtension,
    completionIntegersEmbedding_apply, P.completionExtension_completionEmbedding P' hP,
    Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply P.integers F F',
    ValuationSubring.algebraMap_apply]

/-- The canonical embedding `𝒪'_P →+* 𝒪̂_{P'}` of the local integral closure into the completed
valuation ring is injective. -/
theorem integralClosureToCompletionIntegers_injective :
    Function.Injective (P.integralClosureToCompletionIntegers P' hP) :=
  RingHom.injective_codRestrict.mpr <|
    P'.completionEmbedding.toRingHom.injective.comp Subtype.val_injective

end IntegralClosureMap

end Integers

section Tower

variable {k'' F'' : Type*} [Field k''] [Field F'']
  [Algebra k' k''] [Algebra k k''] [Algebra k'' F''] [Algebra k' F''] [Algebra k F'']
  [Algebra F' F''] [Algebra F F''] [IsScalarTower F F' F'']
  [IsScalarTower k' k'' F''] [IsScalarTower k k'' F'']
  [IsScalarTower k' F' F''] [IsScalarTower k F F'']
  [Algebra.IsIntegral F' F''] (P'' : Place k'' F'') (hP' : P''.restrict k' F' = P')

/-- The canonical embeddings of completed fields compose in a tower, allowing the constant
fields to grow at each step. -/
theorem completionExtension_comp :
    letI : Algebra.IsIntegral F F'' := Algebra.IsIntegral.trans F'
    (P'.completionExtension P'' hP').comp (P.completionExtension P' hP) =
      P.completionExtension P'' (by rw [← restrict_restrict (k₁ := k') (F₁ := F'), hP', hP]) := by
  let : Algebra.IsIntegral F F'' := Algebra.IsIntegral.trans F'
  apply P.eq_completionExtension_of_continuous P'' _
    ((P'.continuous_completionExtension P'' hP').comp (P.continuous_completionExtension P' hP))
  intro x
  simp [← IsScalarTower.algebraMap_apply F F' F'']

end Tower

end Extension

section Constants

variable {k F F' : Type*} [Field k] [Field F] [Field F']
  [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k F')
  (hP : P'.restrict k F = P)

/-- The original constants act through the chosen embedding of completed fields. The scalar
operations are those of the actual algebra structures: the inherited completion scalar action
can have a different presentation. -/
theorem isScalarTower_completionExtensionAlgebra :
    letI := P.completionExtensionAlgebra P' hP
    @IsScalarTower k P.Completion P'.Completion
      (P.instAlgebraCompletion).toSMul (P.completionExtensionAlgebra P' hP).toSMul
      (P'.instAlgebraCompletion).toSMul := by
  let := P.completionExtensionAlgebra P' hP
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [P.algebraMap_completionExtensionAlgebra P' hP]
  simpa only [Algebra.algebraMap_self_apply] using
    (P.completionExtension_algebraMap P' hP c).symm

/-- Completion sends the identity extension to the identity map. -/
@[simp]
theorem completionExtension_self :
    P.completionExtension P (P.restrict_self) = RingHom.id P.Completion := by
  symm
  apply P.eq_completionExtension_of_continuous P P.restrict_self continuous_id
  intro x
  simp

end Constants

section RestrictConstants

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Restricting the constant field of `P'` does not change `completionEmbedding`. -/
@[simp]
theorem completionEmbedding_restrictConstants (P' : Place k' F') (x : F') :
    (P'.restrictConstants k).completionEmbedding x = P'.completionEmbedding x := by
  rw [completionEmbedding_apply, completionEmbedding_apply]

/-- Restricting the constant field of `P'` does not change membership in `𝒪̂_{P'}`. -/
theorem mem_completionPlace_integers_restrictConstants (P' : Place k' F') {z : P'.Completion} :
    z ∈ (P'.restrictConstants k).completionPlace.integers ↔ z ∈ P'.completionPlace.integers := by
  simp

variable [Algebra.IsIntegral F F']

/-- Restricting the constant field of `P'` to `k` does not change `completionExtension`. -/
@[simp]
theorem completionExtension_restrictConstants
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    P.completionExtension (P'.restrictConstants k)
        ((restrict_restrictConstants k F P').trans hP) =
      P.completionExtension P' hP :=
  P.eq_completionExtension_of_continuous P' hP
    (P.continuous_completionExtension (P'.restrictConstants k) _) fun x ↦ by
      rw [P.completionExtension_completionEmbedding (P'.restrictConstants k) _,
        completionEmbedding_restrictConstants]

/-- Restricting the constant field of `P'` to `k` does not change `completionExtensionAlgebra`. -/
@[simp]
theorem completionExtensionAlgebra_restrictConstants
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    P.completionExtensionAlgebra (P'.restrictConstants k)
        ((restrict_restrictConstants k F P').trans hP) =
      P.completionExtensionAlgebra P' hP :=
  congrArg RingHom.toAlgebra (P.completionExtension_restrictConstants P' hP)

end RestrictConstants

end TauCeti.Place
