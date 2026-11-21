/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Degree
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.LinearAlgebra.Basis.Semilinear

/-!
# Degrees and bases after a linearly disjoint extension of constants

Let `F' = F · k'` in a common overfield, with `F` and `k'` linearly disjoint over `k`.
For every intermediate field `C` of `F/k` with `F/C` algebraic, a `C`-basis of `F` remains a
basis of `F'` over `k' · C`. In particular, `[F' : k'(x)] = [F : k(x)]` for every `x ∈ F`, and
when `F` and `F'` carry compatible algebras over `RatFunc k` and `RatFunc k'`, linear independence
over `RatFunc k`, bases of algebraic extensions `F / RatFunc k`, and the degree
`[F : RatFunc k]` all persist over `RatFunc k'`.
The extension `k'/k` can be transcendental; no perfectness or exact-constants hypothesis
is needed once linear disjointness is supplied.

Linear independence is transported by
`IntermediateField.LinearDisjoint.linearIndependent_adjoin_algebraMap_comp`.
Spanning uses algebraicity of `F/C`: adjoining the algebraic image of `F` to `k' · C`
already gives the whole field compositum. A transcendental element also remains
transcendental, so a linearly disjoint extension of constants of a one-variable function
field is again a one-variable function field. Conversely, preserving the finite degree over
a shared transcendental parameter `x` (or over `k(t)`) recovers linear disjointness.

## Main definitions and results

* `TauCeti.constantExtensionBasisOfLinearDisjoint` and `TauCeti.constantExtensionRatFuncBasis`:
  transport a basis over `C` or over `RatFunc k` along a linearly disjoint constant extension,
  together with `TauCeti.constantExtensionRatFuncBasis_repr_algebraMap`.
* `IntermediateField.LinearDisjoint.linearIndependent_ratFunc_algebraMap_comp`: linearly disjoint
  extensions preserve linear independence over `RatFunc`.
* `TauCeti.finrank_over_adjoin_simple_eq_of_linearDisjoint` and
  `TauCeti.finrank_ratFunc_eq_of_linearDisjoint`: preserve the degree over `k(x)` and `RatFunc k`.
* `TauCeti.IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint`: preserve the
  one-variable function-field property under an arbitrary linearly disjoint extension of constants.
* `TauCeti.finrank_eq_of_constantCompositum_eq_top_of_linearDisjoint`,
  `TauCeti.minpoly_map_of_constantCompositum_eq_top_of_linearDisjoint`, and
  `TauCeti.isSeparable_iff_of_constantCompositum_eq_top_of_linearDisjoint`: preserve the degree,
  minimal polynomials, and separability of any relative extension `F / E` on passing to `F' / E'`.
* `TauCeti.linearDisjoint_of_transcendental_of_finrank_eq` and
  `TauCeti.linearDisjoint_of_finrank_ratFunc_eq`: degree preservation over a shared parameter or
  `k(t)` implies linear disjointness of constants.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Section III.6,
  Proposition 3.6.1(c), for the algebraic constant-extension specialization.
* S. Lang, *Algebra*, the theory of linearly disjoint field extensions.
-/

public section

open scoped IntermediateField

namespace TauCeti

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- A basis of an algebraic extension `F/C` stays a basis over `k' · C` in the linearly disjoint
constant compositum `F' = F · k'`. The constants `k'/k` need not be algebraic. -/
noncomputable def constantExtensionBasisOfLinearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) :
    Module.Basis ι (IntermediateField.adjoin k' (Set.range (algebraMap C F'))) F' :=
  Module.Basis.mk (H.linearIndependent_adjoin_algebraMap_comp C b.linearIndependent)
    (span_range_basis_of_isAlgebraic_constantCompositum h C b).ge

/-- The transported basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionBasisOfLinearDisjoint_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (C : IntermediateField k F)
    [Algebra.IsAlgebraic C F] {ι : Type*} (b : Module.Basis ι C F) (i : ι) :
    constantExtensionBasisOfLinearDisjoint H h C b i = algebraMap F F' (b i) :=
  Module.Basis.mk_apply _ _ i

/-- An arbitrary linearly disjoint extension of constants preserves the degree over a
simple intermediate field: `[F · k' : k'(x)] = [F : k(x)]`. -/
theorem finrank_over_adjoin_simple_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) (x : F) :
    Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F := by
  let b := Module.Basis.ofVectorSpace k⟮x⟯ F
  have hadj : IntermediateField.adjoin k' (Set.range (algebraMap k⟮x⟯ F')) =
      k'⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.range_algebraMap_adjoin_simple, IntermediateField.adjoin_adjoin_right]
  by_cases hfin : FiniteDimensional k⟮x⟯ F
  · have : Algebra.IsAlgebraic k⟮x⟯ F := Algebra.IsAlgebraic.of_finite k⟮x⟯ F
    have hdegree :=
      Module.finrank_eq_nat_card_basis (constantExtensionBasisOfLinearDisjoint H h k⟮x⟯ b)
    rwa [hadj, ← Module.finrank_eq_nat_card_basis b] at hdegree
  · have hfin' : ¬ FiniteDimensional k'⟮algebraMap F F' x⟯ F' := fun hfin' ↦ hfin <| by
      have : FiniteDimensional
          (IntermediateField.adjoin k' (Set.range (algebraMap k⟮x⟯ F'))) F' := hadj ▸ hfin'
      have : Finite (Module.Basis.ofVectorSpaceIndex k⟮x⟯ F) :=
        (H.linearIndependent_adjoin_algebraMap_comp k⟮x⟯ b.linearIndependent).finite
      exact Module.Finite.of_basis b
    rw [Module.finrank_of_not_finite hfin', Module.finrank_of_not_finite hfin]

/-- Extending constants linearly disjointly, even transcendently, preserves the one-variable
function-field property. -/
theorem IsFunctionField.of_constantCompositum_eq_top_of_linearDisjoint
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) : IsFunctionField k' F' := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  have := hF.finiteDimensional_adjoin hx
  have := finiteDimensional_adjoin_simple_of_constantCompositum_eq_top (k := k) h x
  exact (H.transcendental_algebraMap hx).isFunctionField_adjoin.finite_extension

section RelativeExtension

variable {E E' : Type*} [Field E] [Field E'] [Algebra k E] [Algebra E F] [IsScalarTower k E F]
  [Algebra k' E'] [Algebra E E'] [Algebra E F'] [Algebra E' F'] [IsScalarTower k' E' F']
  [IsScalarTower E F F'] [IsScalarTower E E' F']

/-- Identify an external compositum `E' = E · k'` inside `F'` with `k'(C)` for `C = im(E → F)`. -/
private noncomputable def subfieldEquivOfConstantCompositum (k : Type u) [Field k]
    [Algebra k F] [Algebra k E] [IsScalarTower k E F] (hE : constantCompositum E k' E' = ⊤) :
    E' ≃+* IntermediateField.adjoin k'
      (Set.range (algebraMap (IsScalarTower.toAlgHom k E F).fieldRange F')) := by
  let ψ := IsScalarTower.toAlgHom k' E' F'
  let C' := IntermediateField.adjoin k'
    (Set.range (algebraMap (IsScalarTower.toAlgHom k E F).fieldRange F'))
  have hsub : ψ.fieldRange.toSubfield = C'.toSubfield := le_antisymm (by
    rintro _ ⟨y, rfl⟩
    have hEC' : ∀ a : E, ψ (algebraMap E E' a) ∈ C'.toSubfield := fun a ↦ by
      change algebraMap E' F' (algebraMap E E' a) ∈ C'
      rw [← IsScalarTower.algebraMap_apply E E' F', IsScalarTower.algebraMap_apply E F F']
      exact IntermediateField.subset_adjoin k' _ ⟨⟨algebraMap E F a, ⟨a, rfl⟩⟩, rfl⟩
    exact ((constantCompositum_le_iff E k' E'
      (K := (C'.toSubfield.comap ψ.toRingHom).toIntermediateField hEC')).mpr fun c ↦ by
        change ψ (algebraMap k' E' c) ∈ C'; rw [ψ.commutes]; exact C'.algebraMap_mem c)
      (hE ▸ IntermediateField.mem_top)) (IntermediateField.adjoin_le_iff.mpr <| by
        rintro _ ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
        exact ⟨algebraMap E E' a, by
          change algebraMap E' F' (algebraMap E E' a) = algebraMap F F' (algebraMap E F a)
          rw [← IsScalarTower.algebraMap_apply E E' F', ← IsScalarTower.algebraMap_apply E F F']⟩)
  exact ψ.equivFieldRange.toRingEquiv.trans (RingEquiv.subfieldCongr hsub)

@[simp]
private theorem subfieldEquivOfConstantCompositum_coe (k : Type u) [Field k] [Algebra k F]
    [Algebra k E] [IsScalarTower k E F] (hE : constantCompositum E k' E' = ⊤) (c : E') :
    (subfieldEquivOfConstantCompositum k (F := F) (F' := F') hE c : F') = algebraMap E' F' c :=
  rfl

/-- **Linearly disjoint constant extension preserves minimal polynomials over subextensions.**
Let `F' = F · k'` with `k'` linearly disjoint from `F` over `k`, and let `E' = E · k'` for a field
`E` between `k` and `F`. Every element `x ∈ F` integral over `E` has minimal polynomial over `E'`
equal to the base change of `minpoly E x`. Neither `k' / k` nor `F / E` need be finite. -/
theorem minpoly_map_of_constantCompositum_eq_top_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hE : constantCompositum E k' E' = ⊤) {x : F} (hx : IsIntegral E x) :
    minpoly E' (algebraMap F F' x) = (minpoly E x).map (algebraMap E E') := by
  let f := IsScalarTower.toAlgHom k E F
  let eE := f.equivFieldRange
  let eE' := subfieldEquivOfConstantCompositum k (F := F) (F' := F') hE
  have heE (c : f.fieldRange) : algebraMap E F (eE.symm c) = c :=
    congrArg Subtype.val (eE.apply_symm_apply c)
  let pb := IntermediateField.adjoin.powerBasis hx
  have hliE : LinearIndependent E (fun i : Fin pb.dim ↦ x ^ (i : ℕ)) := by
    convert pb.basis.linearIndependent.map' (E⟮x⟯).val.toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective) with i; simp [pb]
  have hliC' := H.linearIndependent_adjoin_algebraMap_comp f.fieldRange
    (hliE.map_of_injective_injective eE.symm (AddMonoidHom.id F) (by simp) (by simp)
      fun c y ↦ by simp [Algebra.smul_def, heE])
  have hliE' : LinearIndependent E' (fun i : Fin pb.dim ↦ algebraMap F F' x ^ (i : ℕ)) := by
    convert hliC'.map_of_injective_injective eE' (AddMonoidHom.id F') (by simp) (by simp)
      (fun c y ↦ by simp [Algebra.smul_def, eE']) with i; simp
  let x' := algebraMap F F' x
  have hx' : IsIntegral E' x' := (hx.map (IsScalarTower.toAlgHom E F F')).tower_top
  have hliSub : LinearIndependent E'
      (fun i : Fin pb.dim ↦ (IntermediateField.AdjoinSimple.gen E' x') ^ (i : ℕ)) :=
    LinearIndependent.of_comp (E'⟮x'⟯).val.toLinearMap (by convert hliE' with i; simp [x'])
  have := IntermediateField.adjoin.finiteDimensional hx'
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx')
    ((minpoly.monic hx).map _) (minpoly.dvd_map_of_isScalarTower' E E' F' x) ?_).symm
  rw [(minpoly.monic hx).natDegree_map, ← IntermediateField.adjoin.finrank hx']
  simpa [pb, IntermediateField.adjoin.powerBasis_dim hx] using hliSub.fintype_card_le_finrank

/-- **Linearly disjoint constant extension preserves relative degrees.** Let `F' = F · k'` with `k'`
linearly disjoint from `F` over `k`, and let `E' = E · k'` for a field `E` between `k` and `F`.
Then `[F' : E'] = [F : E]`, with no algebraicity or finiteness assumption on `k' / k` or `F / E`. -/
theorem finrank_eq_of_constantCompositum_eq_top_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hE : constantCompositum E k' E' = ⊤) (hF : constantCompositum F k' F' = ⊤) :
    Module.finrank E' F' = Module.finrank E F := by
  let f := IsScalarTower.toAlgHom k E F
  let C := f.fieldRange
  let C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  let eE := f.equivFieldRange
  let eE' := subfieldEquivOfConstantCompositum k (F := F) (F' := F') hE
  have heE (c : C) : algebraMap E F (eE.symm c) = c := congrArg Subtype.val (eE.apply_symm_apply c)
  have heE' (c : C') : algebraMap E' F' (eE'.symm c) = c :=
    congrArg Subtype.val (eE'.apply_symm_apply c)
  by_cases hAlg : Algebra.IsAlgebraic E F
  · have : Algebra.IsAlgebraic C F := ⟨fun y ↦
      let ⟨p, hp0, hpy⟩ := hAlg.isAlgebraic y
      ⟨p.map eE.toRingHom, Polynomial.map_ne_zero hp0,
        by rwa [Polynomial.aeval_def, Polynomial.eval₂_map]⟩⟩
    let b := Module.Basis.ofVectorSpace E F
    let bC := b.mapCoeffs eE.toRingEquiv fun c y ↦ by
      simp [Algebra.smul_def, eE, f, AlgHom.equivFieldRange_apply_coe]
    let b' := (constantExtensionBasisOfLinearDisjoint H hF C bC).mapCoeffs eE'.symm fun c y ↦ by
      simp [Algebra.smul_def, heE']
    exact (Module.finrank_eq_nat_card_basis b').trans (Module.finrank_eq_nat_card_basis b).symm
  · have hnE : ¬ Module.Finite E F := fun hf ↦ hAlg (Algebra.IsAlgebraic.of_finite E F)
    rw [Module.finrank_of_not_finite hnE]
    refine Module.finrank_of_not_finite fun hf' ↦ hnE ?_
    let b' := Module.Basis.ofVectorSpace E' F'
    have : Finite (Module.Basis.ofVectorSpaceIndex E' F') := Module.Finite.finite_basis b'
    have hfinC' : Module.Finite C' F' := Module.Finite.of_basis
      (b'.mapCoeffs eE' fun _ _ ↦ by rw [Algebra.smul_def, Algebra.smul_def]; rfl)
    have hlt : Cardinal.lift.{v'} (Module.rank C F) < Cardinal.aleph0 :=
      (H.lift_rank_le_lift_rank_adjoin_algebraMap C).trans_lt
        (by simpa using Module.rank_lt_aleph0 C' F')
    have hfinC : Module.Finite C F := Module.rank_lt_aleph0_iff.mp (by simpa using hlt)
    let bC := Module.Basis.ofVectorSpace C F
    have : Finite (Module.Basis.ofVectorSpaceIndex C F) := Module.Finite.finite_basis bC
    exact Module.Finite.of_basis
      (bC.mapCoeffs eE.symm.toRingEquiv fun c y ↦ by simp [Algebra.smul_def, heE])

/-- **Linearly disjoint constant extension preserves separability of algebraic relative
extensions.** Let `F' = F · k'` with `k'` linearly disjoint from `F` over `k`, and `E' = E · k'`
for a field `E` between `k` and `F` with `F / E` algebraic. Then `F' / E'` is separable if and
only if `F / E` is separable, for arbitrary (possibly transcendental or inseparable) `k' / k`. -/
theorem isSeparable_iff_of_constantCompositum_eq_top_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hE : constantCompositum E k' E' = ⊤) (hF : constantCompositum F k' F' = ⊤)
    [Algebra.IsAlgebraic E F] :
    Algebra.IsSeparable E' F' ↔ Algebra.IsSeparable E F := by
  have hsep_el (x : F) : IsSeparable E' (algebraMap F F' x) ↔ IsSeparable E x := by
    rw [IsSeparable, IsSeparable, minpoly_map_of_constantCompositum_eq_top_of_linearDisjoint H hE
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral, Polynomial.separable_map]
  refine ⟨fun h ↦ ⟨fun x ↦ (hsep_el x).mp (Algebra.IsSeparable.isSeparable E' _)⟩, fun h ↦ ?_⟩
  let L := IntermediateField.adjoin E' (Set.range (algebraMap F F'))
  have htop : L = ⊤ := top_le_iff.mp fun z _ ↦ by
    have hle := (constantCompositum_le_iff F k' F' (K := L.toSubfield.toIntermediateField
      fun a ↦ IntermediateField.subset_adjoin E' _ ⟨a, rfl⟩)).mpr fun c ↦ by
        change algebraMap k' F' c ∈ L
        rw [IsScalarTower.algebraMap_apply k' E' F' c]
        exact L.algebraMap_mem (algebraMap k' E' c)
    exact (hF ▸ hle) IntermediateField.mem_top
  rw [← IntermediateField.isSeparable_top, ← htop,
    IntermediateField.isSeparable_adjoin_iff_isSeparable]
  rintro _ ⟨x, rfl⟩
  exact (hsep_el x).mpr (Algebra.IsSeparable.isSeparable E x)

end RelativeExtension

/-- **Linear disjointness over a shared parameter from degree preservation.** -/
theorem linearDisjoint_of_transcendental_of_finrank_eq (h : constantCompositum F k' F' = ⊤) {x : F}
    (hx' : Transcendental k' (algebraMap F F' x)) [FiniteDimensional k⟮x⟯ F]
    (hn : Module.finrank k'⟮algebraMap F F' x⟯ F' = Module.finrank k⟮x⟯ F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  let b := Module.finBasis k⟮x⟯ F
  have hspan := span_range_basis_of_isAlgebraic_constantCompositum h k⟮x⟯ b
  rw [IntermediateField.range_algebraMap_adjoin_simple,
    IntermediateField.adjoin_adjoin_right] at hspan
  exact IntermediateField.linearDisjoint_of_transcendental_of_linearIndependent hx' b
    (linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by rw [Fintype.card_fin, ← hn]))

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

/-- **Degree preservation over `k(t)` implies linear disjointness of constants.** -/
theorem linearDisjoint_of_finrank_ratFunc_eq [FiniteDimensional (RatFunc k) F]
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (hn : Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F) :
    (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F := by
  have hx' : Transcendental k' (algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X)) :=
    hX ▸ (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k') F')).mpr RatFunc.transcendental_X
  have : FiniteDimensional k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    Module.finite_of_finrank_pos
      (finrank_adjoin_algebraMap_X (k := k) (F := F) ▸ Module.finrank_pos)
  refine linearDisjoint_of_transcendental_of_finrank_eq h hx' ?_
  rw [hX, finrank_adjoin_algebraMap_X, finrank_adjoin_algebraMap_X, hn]

/-- **Linearly disjoint extensions preserve linear independence over `RatFunc`**: if the images of
`k'` and `F` in `F'` are linearly disjoint over `k` and `RatFunc.X` acts compatibly on `F` and
`F'`, then any `RatFunc k`-linearly independent family in `F` maps to a `RatFunc k'`-linearly
independent family in `F'`. Neither algebraicity of `k' / k` nor algebraicity of `F / RatFunc k`
is required. -/
theorem _root_.IntermediateField.LinearDisjoint.linearIndependent_ratFunc_algebraMap_comp
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} {c : ι → F} (hc : LinearIndependent (RatFunc k) c) :
    LinearIndependent (RatFunc k') (algebraMap F F' ∘ c) := by
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  have hc₁ : LinearIndependent k⟮algebraMap (RatFunc k) F RatFunc.X⟯ c := by
    simpa using hc.map_of_surjective_injectiveₛ (RatFunc.algEquivOfTranscendental _ hx) (.id F)
      (RatFunc.algEquivOfTranscendental _ hx).surjective Function.injective_id
      fun r m ↦ (algEquivOfTranscendental_algebraMap_X_smul r m).symm
  simpa using (H.linearIndependent_adjoin_algebraMap_comp _ hc₁).map_of_surjective_injectiveₛ
    (adjoinRangeAlgEquivRatFunc hX) (.id F') (adjoinRangeAlgEquivRatFunc hX).surjective
    Function.injective_id fun r m ↦ (adjoinRangeAlgEquivRatFunc_smul hX r m).symm

/-- **Transport of a `RatFunc k`-basis along a linearly disjoint extension of constants.**
If `F' = F · k'` linearly disjointly over `k`, `F / RatFunc k` is algebraic, and the rational
variable `X` acts compatibly on `F` and `F'`, any `RatFunc k`-basis of `F` maps to a
`RatFunc k'`-basis of `F'`. The constant extension `k' / k` may be transcendental. -/
noncomputable def constantExtensionRatFuncBasis
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc k') F' :=
  haveI := (isAlgebraic_adjoin_algebraMap_X_iff (k := k) (F := F)).mpr ‹_›
  have hx : Transcendental k (algebraMap (RatFunc k) F RatFunc.X) :=
    (transcendental_algebraMap_iff
      (FaithfulSMul.algebraMap_injective (RatFunc k) F)).mpr RatFunc.transcendental_X
  (constantExtensionBasisOfLinearDisjoint H h _
    (b.mapCoeffs (RatFunc.algEquivOfTranscendental _ hx).toRingEquiv
      (fun _ _ ↦ by simp))).mapCoeffs
    (adjoinRangeAlgEquivRatFunc hX).toRingEquiv (fun _ _ ↦ by simp)

/-- The transported `RatFunc k'`-basis consists of the images of the original basis vectors. -/
@[simp]
theorem constantExtensionRatFuncBasis_apply
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    constantExtensionRatFuncBasis H h hX b i = algebraMap F F' (b i) := by
  simp [constantExtensionRatFuncBasis]

/-- **Linearly disjoint constant extensions preserve degree over the rational function field.**
If `F' = F · k'` linearly disjointly over `k` and `X` acts compatibly on `F` and `F'`, then
`[F' : RatFunc k'] = [F : RatFunc k]`. Unlike
`TauCeti.finrank_ratFunc_eq_of_constantCompositum_eq_top`, the extension `k' / k` may be
transcendental or inseparable once linear disjointness holds. -/
theorem finrank_ratFunc_eq_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F := by
  rw [← finrank_adjoin_algebraMap_X (k := k') (F := F'), ← hX,
    finrank_over_adjoin_simple_eq_of_linearDisjoint H h, finrank_adjoin_algebraMap_X]

/-- The coordinates of an element of `F` in `constantExtensionRatFuncBasis` are the images of its
coordinates over `RatFunc k`. -/
@[simp]
theorem constantExtensionRatFuncBasis_repr_algebraMap
    [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤)
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    (hXF : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    [Algebra.IsAlgebraic (RatFunc k) F] {ι : Type*} (b : Module.Basis ι (RatFunc k) F)
    (x : F) (i : ι) :
    (constantExtensionRatFuncBasis H h hXF b).repr (algebraMap F F' x) i =
      algebraMap (RatFunc k) (RatFunc k') (b.repr x i) := by
  let φ : F →ₛₗ[algebraMap (RatFunc k) (RatFunc k')] F' :=
    { toFun := algebraMap F F'
      map_add' := map_add _
      map_smul' := fun r y ↦ by
        simp [Algebra.smul_def, ← algebraMap_ratFunc_apply_eq hX hXF] }
  have hφ : φ = b.semilinearMap (algebraMap (RatFunc k) (RatFunc k'))
      (constantExtensionRatFuncBasis H h hXF b) :=
    b.ext fun j ↦ by simp [φ]
  simpa [φ] using congrArg ((constantExtensionRatFuncBasis H h hXF b).repr · i)
    (LinearMap.congr_fun hφ x)

end RatFunc

end TauCeti
