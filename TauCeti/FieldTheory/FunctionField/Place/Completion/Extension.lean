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
extended valuation is the original completed valuation raised to the ramification index
(`valuation_completionExtension`, `ord_completionExtension`), so completion preserves the
ramification index `e(P' ∣ P)` (`ramificationIdx_completionPlace`). The induced algebra structure
makes the completed extension available for local Galois theory.

The algebra structure is explicit, since choosing different places above `P` gives different
completed extensions. Install `completionExtensionAlgebra` locally. The induced scalar tower
`isScalarTower_restrictConstants_completion` identifies the canonical constant action
`k → k' → P'.Completion`, and `isScalarTower_completionExtensionAlgebra` identifies the base
constant action through the completed extension. Every element of `F'` remains separable over
`F̂_P` inside `F̂'_{P'}` when `F' / F` is separable (`isSeparable_completionEmbedding`). The
completed extension restricts to an injective local homomorphism `completionIntegersExtension` of
completed valuation rings, whose algebra `completionIntegersExtensionAlgebra` is likewise installed
locally and makes `𝒪̂_{P'}` a torsion-free `𝒪̂_P`-subalgebra of `F̂_{P'}`
(`isScalarTower_completionIntegersExtensionAlgebra`, `isTorsionFree_completionIntegers`), and the
local integral closure `𝒪'_P` embeds injectively into `𝒪̂_{P'}` via
`completionIntegersIntegralClosureHom`. No finiteness, separability, or residue-field assumptions
are needed.

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
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 :=
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

/-- Completion preserves the ramification index, with no finiteness assumption on the residue
extension. -/
@[simp]
theorem ramificationIdx_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    ramificationIdx P.Completion P'.completionPlace = ramificationIdx F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  rw [ramificationIdx_def,
    Valuation.ordIndex_eq_mul_of_forall_ord_eq _ P.completionPlace.valuation (fun x ↦ by
      rw [Valuation.ord_comap, ord_valuation, ord_valuation, algebraMap_completionExtensionAlgebra,
        P.ord_completionExtension P' hP x]),
    Valuation.ordIndex_eq_one_of_surjective _ P.completionPlace.valuation_surjective, mul_one]

/-- Through the completed extension, the embedding of `F'` in its completion is semilinear over
the embedding of `F` in its completion. -/
theorem completionEmbedding_smul (c : F) (y : F') :
    letI := P.completionExtensionAlgebra P' hP
    P'.completionEmbedding (c • y) = P.completionEmbedding c • P'.completionEmbedding y := by
  let _ := P.completionExtensionAlgebra P' hP
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, algebraMap_completionExtensionAlgebra,
    completionExtension_completionEmbedding]

/-- The extended embedding respects the original embeddings of the constant fields. -/
theorem completionExtension_algebraMap (c : k) :
    P.completionExtension P' hP (algebraMap k P.Completion c) =
      algebraMap k' P'.Completion (algebraMap k k' c) := by
  rw [← P.completionEmbedding.commutes c,
    completionExtension_completionEmbedding, ← IsScalarTower.algebraMap_apply k F F',
    IsScalarTower.algebraMap_apply k k' F', P'.completionEmbedding.commutes]

/-- Every element of `F'` remains separable over `F̂_P` inside `F̂_{P'}`. -/
theorem isSeparable_completionEmbedding [Algebra.IsSeparable F F'] (y : F') :
    letI := P.completionExtensionAlgebra P' hP
    IsSeparable P.Completion (P'.completionEmbedding y) := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionAlgebra
  let _ := P'.completionAlgebra
  let _ : Algebra F P'.Completion :=
    haveI := WithVal.uniformContinuousConstSMul_of_isScalarTower F P'.valuation
    UniformSpace.Completion.algebra (WithVal P'.valuation) F
  have hFP' (x : F) :
      algebraMap F P'.Completion x = P'.completionEmbedding (algebraMap F F' x) := by
    rw [UniformSpace.Completion.algebraMap_def, WithVal.algebraMap_right_apply,
      P'.completionEmbedding_apply]
  have : IsScalarTower F F' P'.Completion := .of_algebraMap_eq fun x ↦ by
    rw [hFP', algebraMap_completion]
  have : IsScalarTower F P.Completion P'.Completion := .of_algebraMap_eq fun x ↦ by
    rw [hFP', algebraMap_completion, algebraMap_completionExtensionAlgebra,
      completionExtension_completionEmbedding]
  simpa only [IsScalarTower.coe_toAlgHom', algebraMap_completion] using
    ((Algebra.IsSeparable.isSeparable F y).map
      (IsScalarTower.toAlgHom F F' P'.Completion) (RingHom.injective _)).tower_top P.Completion

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

/-- The completed valuation-ring extension forms a scalar tower inside the completed upper field. -/
instance isScalarTower_completionIntegersExtensionAlgebra :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    P.algebraMap_completionExtensionAlgebra P' hP, ValuationSubring.algebraMap_apply,
    ValuationSubring.algebraMap_apply, P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP]

/-- The completed valuation ring `𝒪̂_{P'}` is torsion-free over `𝒪̂_P`. -/
instance isTorsionFree_completionIntegers :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr fun a b hab ↦ Subtype.ext ?_
  have hab' := congrArg Subtype.val hab
  rw [P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP,
    P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP] at hab'
  exact (P.completionExtension P' hP).injective hab'

section IntegralClosure

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- The canonical `𝒪_P`-algebra homomorphism from the local integral closure `𝒪'_P` to the
completed valuation ring `𝒪̂_{P'}` at a place `P'` lying over `P`. -/
noncomputable def completionIntegersIntegralClosureHom :
    letI : Algebra P.integers P'.completionPlace.integers :=
      ((P.completionIntegersExtension P' hP).comp P.completionIntegersEmbedding.toRingHom).toAlgebra
    integralClosure P.integers F' →ₐ[P.integers] P'.completionPlace.integers :=
  letI : Algebra P.integers P'.completionPlace.integers :=
    ((P.completionIntegersExtension P' hP).comp P.completionIntegersEmbedding.toRingHom).toAlgebra
  ⟨P'.completionIntegersEmbedding.toRingHom.comp
      ((algebraMap (integralClosure P.integers F') F').codRestrict P'.integers fun b ↦ by
        subst hP
        exact algebraMap_mem_integers_of_mem_integralClosure k F P' b),
    fun r ↦ Subtype.ext <| by
      simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply P.integers F F']⟩

/-- Coercing `completionIntegersIntegralClosureHom` to `F̂_{P'}` is `P'.completionEmbedding`. -/
@[simp]
theorem coe_completionIntegersIntegralClosureHom (b : integralClosure P.integers F') :
    (P.completionIntegersIntegralClosureHom P' hP b : P'.Completion) =
      P'.completionEmbedding (b : F') := by
  dsimp [completionIntegersIntegralClosureHom]
  exact P'.completionIntegersEmbedding_apply _

/-- On `𝒪_P`, `completionIntegersIntegralClosureHom` agrees with `completionIntegersExtension`. -/
theorem completionIntegersIntegralClosureHom_algebraMap (r : P.integers) :
    P.completionIntegersIntegralClosureHom P' hP
        (algebraMap P.integers (integralClosure P.integers F') r) =
      P.completionIntegersExtension P' hP (P.completionIntegersEmbedding r) := by
  apply Subtype.ext
  rw [coe_completionIntegersIntegralClosureHom]
  simp [IsScalarTower.algebraMap_apply P.integers F F']

/-- The canonical homomorphism `𝒪'_P →ₐ[𝒪_P] 𝒪̂_{P'}` is injective. -/
theorem completionIntegersIntegralClosureHom_injective :
    Function.Injective (P.completionIntegersIntegralClosureHom P' hP) := fun _ _ h ↦
  Subtype.ext <| P'.completionEmbedding.toRingHom.injective <| by
    simpa only [coe_completionIntegersIntegralClosureHom, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe] using congrArg Subtype.val h

end IntegralClosure

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

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

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

variable (k) in
/-- The canonical constant-field action on `P'.Completion` (from `P'.restrictConstants k`)
factors through `k → k' → P'.Completion`. -/
theorem isScalarTower_restrictConstants_completion (P' : Place k' F') :
    letI := (P'.restrictConstants k).instAlgebraCompletion
    @IsScalarTower k k' P'.Completion Algebra.toSMul P'.instAlgebraCompletion.toSMul
      (P'.restrictConstants k).instAlgebraCompletion.toSMul := by
  let _ := (P'.restrictConstants k).instAlgebraCompletion
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  change algebraMap k P'.Completion c = algebraMap k' P'.Completion (algebraMap k k' c)
  rw [← (P'.restrictConstants k).completionEmbedding.commutes c,
    ← P'.completionEmbedding.commutes (algebraMap k k' c),
    completionEmbedding_restrictConstants, IsScalarTower.algebraMap_apply k k' F']

/-- Restricting the constant field of `P'` commutes with `completionPlace` under the induced
scalar tower `k → k' → P'.Completion`. -/
@[simp]
theorem completionPlace_restrictConstants (P' : Place k' F') :
    letI := (P'.restrictConstants k).instAlgebraCompletion
    haveI := P'.isScalarTower_restrictConstants_completion k
    (P'.restrictConstants k).completionPlace =
      @Place.restrictConstants k' P'.Completion _ _ P'.instAlgebraCompletion
        k _ _ (P'.restrictConstants k).instAlgebraCompletion this P'.completionPlace := by
  ext x
  simp

variable [Algebra.IsIntegral F F']

/-- The base constants act on `P'.Completion` (via `P'.restrictConstants k`) through the chosen
embedding of completed fields. The scalar operations are those of the actual algebra structures:
the inherited completion scalar action can have a different presentation. -/
theorem isScalarTower_completionExtensionAlgebra
    (P : Place k F) (P' : Place k' F') (hP : P'.restrict k F = P) :
    letI := P.completionExtensionAlgebra P' hP
    letI := (P'.restrictConstants k).instAlgebraCompletion
    @IsScalarTower k P.Completion P'.Completion
      (P.instAlgebraCompletion).toSMul (P.completionExtensionAlgebra P' hP).toSMul
      ((P'.restrictConstants k).instAlgebraCompletion).toSMul := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := (P'.restrictConstants k).instAlgebraCompletion
  have := P'.isScalarTower_restrictConstants_completion k
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [P.algebraMap_completionExtensionAlgebra P' hP, P.completionExtension_algebraMap P' hP c,
    ← IsScalarTower.algebraMap_apply k k' P'.Completion]

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
