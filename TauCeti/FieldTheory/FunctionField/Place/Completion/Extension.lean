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
through the completed extension; in general, `completionAlgebraBase` equips `P'.Completion` with
the composite `k`-algebra structure factoring through both `k'` and `P.Completion`, and
`Place.restrictScalars` restricts the constant field of `P'` to `k` without changing its valuation
or completion. The completed extension preserves the ramification index
(`ramificationIdx_completionPlace`) and restricts to an injective local homomorphism
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

/-- Completion preserves the ramification index over the place below, with no finiteness or
separability assumptions. -/
@[simp]
theorem ramificationIdx_completionPlace :
    letI := P.completionExtensionAlgebra P' hP
    ramificationIdx P.Completion P'.completionPlace = ramificationIdx F P' := by
  let _ := P.completionExtensionAlgebra P' hP
  rw [ramificationIdx_def, Valuation.ordIndex_eq_mul_of_forall_ord_eq _ P.completionPlace.valuation
      (e := ramificationIdx F P') fun x ↦ ?_,
    Valuation.ordIndex_eq_one_of_surjective _ P.completionPlace.valuation_surjective, mul_one]
  simpa only [Valuation.ord_comap, algebraMap_completionExtensionAlgebra, ← ord_valuation] using
    P.ord_completionExtension P' hP x

/-- Through the constants `k'`, the completion at `P'` is a `k`-algebra. Like
`TauCeti.Place.integersAlgebraBase`, this is not a global instance, since for `k = k'` it would
compete with `TauCeti.Place.instAlgebraCompletion`. Install it locally together with
`TauCeti.Place.isScalarTower_completionAlgebraBase` and
`TauCeti.Place.isScalarTower_completionAlgebraBase_completionExtension`. -/
@[instance_reducible]
noncomputable def completionAlgebraBase : Algebra k P'.Completion :=
  ((algebraMap k' P'.Completion).comp (algebraMap k k')).toAlgebra

omit [Algebra k F'] [IsScalarTower k k' F'] in
/-- The `k`-algebra `completionAlgebraBase` on `P'.Completion` factors through `k'`. As in
`TauCeti.Place.isScalarTower_completionExtensionAlgebra`, the scalar actions are those of the
algebra structures rather than the inherited uniform-completion actions. -/
theorem isScalarTower_completionAlgebraBase :
    letI := completionAlgebraBase (k := k) P'
    @IsScalarTower k k' P'.Completion _
      (P'.instAlgebraCompletion).toSMul (completionAlgebraBase (k := k) P').toSMul :=
  letI := completionAlgebraBase (k := k) P'
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The `k`-algebra `completionAlgebraBase` on `P'.Completion` factors through `P.Completion`. -/
theorem isScalarTower_completionAlgebraBase_completionExtension :
    letI := P.completionExtensionAlgebra P' hP
    letI := completionAlgebraBase (k := k) P'
    @IsScalarTower k P.Completion P'.Completion
      (P.instAlgebraCompletion).toSMul (P.completionExtensionAlgebra P' hP).toSMul
      (completionAlgebraBase (k := k) P').toSMul := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := completionAlgebraBase (k := k) P'
  refine IsScalarTower.of_algebraMap_eq fun c ↦ ?_
  rw [P.algebraMap_completionExtensionAlgebra P' hP, P.completionExtension_algebraMap P' hP]
  rfl

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

/-- The map of completed valuation rings is injective, being a restriction of an embedding of
fields. -/
theorem completionIntegersExtension_injective :
    Function.Injective (P.completionIntegersExtension P' hP) := fun _ _ h ↦
  Subtype.ext <| (P.completionExtension P' hP).injective (congrArg Subtype.val h)

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

/-- The completed valuation ring of `P'` is torsion-free over that of `P`. -/
instance isTorsionFree_completionIntegersExtensionAlgebra :
    letI := P.completionIntegersExtensionAlgebra P' hP
    Module.IsTorsionFree P.completionPlace.integers P'.completionPlace.integers := by
  let _ := P.completionIntegersExtensionAlgebra P' hP
  rw [Module.isTorsionFree_iff_algebraMap_injective, algebraMap_completionIntegersExtensionAlgebra]
  exact P.completionIntegersExtension_injective P' hP

/-- The chosen algebra map of completed valuation rings is the completed extension. -/
theorem coe_algebraMap_completionIntegersExtensionAlgebra (x : P.completionPlace.integers) :
    letI := P.completionIntegersExtensionAlgebra P' hP
    (algebraMap P.completionPlace.integers P'.completionPlace.integers x : P'.Completion) =
      P.completionExtension P' hP x :=
  (rfl)

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension in
/-- The completed valuation rings and the upper completed field form a scalar tower. -/
theorem isScalarTower_completionIntegersExtensionAlgebra :
    letI := P.completionExtensionAlgebra P' hP
    letI := P.completionIntegersExtensionAlgebra P' hP
    IsScalarTower P.completionPlace.integers P'.completionPlace.integers P'.Completion := by
  let _ := P.completionExtensionAlgebra P' hP
  let _ := P.completionIntegersExtensionAlgebra P' hP
  refine .of_algebraMap_eq fun x ↦ ?_
  rw [IsScalarTower.algebraMap_apply P.completionPlace.integers P.Completion P'.Completion,
    P.algebraMap_completionExtensionAlgebra P' hP]
  exact (P.coe_algebraMap_completionIntegersExtensionAlgebra P' hP x).symm

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

section RestrictScalars

variable (k : Type*) {k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Restricting the constant field of `P' : Place k' F'` to `k` produces a place of `F' / k` with
the same valuation and completion, with no integrality assumption on `k' / k`. -/
abbrev restrictScalars (P' : Place k' F') : Place k F' where
  valuation := P'.valuation
  valuation_surjective := P'.valuation_surjective
  isTrivialOn := ⟨fun c hc ↦ by
    rw [IsScalarTower.algebraMap_apply k k' F']
    exact P'.isTrivialOn.eq_one _ ((map_ne_zero (algebraMap k k')).mpr hc)⟩

variable {k}

@[simp]
theorem valuation_restrictScalars (P' : Place k' F') :
    (P'.restrictScalars k).valuation = P'.valuation :=
  (rfl)

@[simp]
theorem completionEmbedding_restrictScalars (P' : Place k' F') (x : F') :
    (P'.restrictScalars k).completionEmbedding x = P'.completionEmbedding x :=
  ((P'.restrictScalars k).completionEmbedding_apply x).trans (P'.completionEmbedding_apply x).symm

variable [Algebra.IsIntegral F F']

@[simp]
theorem restrict_restrictScalars (P' : Place k' F') :
    (P'.restrictScalars k).restrict k F = P'.restrict k F := by
  rw [restrict_eq_iff_integers_le]
  intro x hx
  rw [(P'.restrictScalars k).mem_integers_iff]
  exact P'.mem_integers_iff.mp ((mem_integers_restrict_iff k F P' x).mp hx)

theorem completionExtension_restrictScalars (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    P.completionExtension (P'.restrictScalars k)
        ((P'.restrict_restrictScalars (k := k) (F := F)).trans hP) =
      P.completionExtension P' hP :=
  P.eq_completionExtension_of_continuous P' hP
    (P.continuous_completionExtension (P'.restrictScalars k) _)
    fun x ↦ (P.completionExtension_completionEmbedding _ _ x).trans
      (P'.completionEmbedding_restrictScalars (algebraMap F F' x))

theorem completionExtensionAlgebra_restrictScalars (P : Place k F) (P' : Place k' F')
    (hP : P'.restrict k F = P) :
    P.completionExtensionAlgebra (P'.restrictScalars k)
        ((P'.restrict_restrictScalars (k := k) (F := F)).trans hP) =
      P.completionExtensionAlgebra P' hP :=
  congrArg RingHom.toAlgebra (P.completionExtension_restrictScalars P' hP)

end RestrictScalars

end TauCeti.Place
