/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup
public import TauCeti.NumberTheory.LocalField.Unramified.Frobenius
public import TauCeti.Topology.Algebra.PointTopology.Group

/-!
# Rational points as Frobenius fixed points over `Breve E`

Let `E` be a nonarchimedean local field, `Breve E` the completion of its maximal unramified
extension and `σ = TauCeti.MaxUnramifiedCompletion.frobenius E` its arithmetic Frobenius. For an
affine `E`-scheme `X = Spec A`, the Frobenius acts on `X(Breve E) = Hom_E(A, Breve E)` by
`x ↦ σ ∘ x`. Since the fixed field of `σ` is `E`
(`TauCeti.MaxUnramifiedCompletion.fixedPoints_frobenius`), a point is fixed by this action exactly
when all its values lie in `E`, that is, exactly when it comes from `X(E)`:
`X(E) = X(Breve E)^σ`. The same holds integrally: for an `𝒪[E]`-algebra `A`, the
`𝒪[Breve E]`-valued points fixed by `σ` are the `𝒪[E]`-valued points, because the fixed ring of
`σ` on `𝒪[Breve E]` is `𝒪[E]` (`TauCeti.MaxUnramifiedCompletion.fixedPoints_integerFrobenius`).

For an affine group `G = Spec H`, the action of `σ` is the group endomorphism
`AlgHom.mapValue σ` of `G(Breve E)`, continuous for the point topology
(`AlgHom.continuous_mapValue` with `TauCeti.MaxUnramifiedCompletion.continuous_frobenius`). Its
fixed subgroup is the image of `G(E)`. Since `E` is a closed subfield of `Breve E`
(`TauCeti.MaxUnramifiedCompletion.isClosedEmbedding_algebraMap`), the inclusion `G(E) → G(Breve E)`
is a closed embedding (`AlgHom.isClosedEmbedding_mapValue`), so `G(E)` is isomorphic to that fixed
subgroup as a topological group. In the same way the integral points `𝒢(𝒪[E])` of an affine group
over `𝒪[E]` are the `σ`-fixed points of `𝒢(𝒪[Breve E])`. This is how rational and integral points
of a group over a local field are recovered from its points over `Breve E`, the setting of the
Iwahori–Weyl group and the Kottwitz homomorphism.

## Main results

* `TauCeti.MaxUnramifiedCompletion.range_ofId_comp`,
  `TauCeti.MaxUnramifiedCompletion.range_ofId_comp_integer`: the points of an affine scheme with
  values in `E` (respectively `𝒪[E]`) are the points with values in `Breve E` (respectively
  `𝒪[Breve E]`) fixed by `σ`.
* `TauCeti.MaxUnramifiedCompletion.range_mapValue_ofId`,
  `TauCeti.MaxUnramifiedCompletion.range_mapValue_ofId_integer`: for an affine group, the image of
  `G(E)` in `G(Breve E)` (respectively of `𝒢(𝒪[E])` in `𝒢(𝒪[Breve E])`) is the subgroup fixed by
  `σ`.
* `TauCeti.MaxUnramifiedCompletion.rationalPointsContinuousMulEquiv`: `G(E) ≃ G(Breve E)^σ` as
  topological groups, with `coe_rationalPointsContinuousMulEquiv` and
  `algebraMap_rationalPointsContinuousMulEquiv_symm_apply_apply` describing it and its inverse.

## References

* X. He, *Some results on affine Deligne–Lusztig varieties*, Proc. ICM 2018, §4.3.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, Compositio Math. 109 (1997), §1.1.
-/

public section

open ValuativeRel AlgHom

namespace TauCeti.MaxUnramifiedCompletion

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-! ### Points of affine schemes -/

/-- **Rational points are the Frobenius-fixed points.** For an affine `E`-scheme `X = Spec A`, a
point with values in `Breve E` comes from a point with values in `E` exactly when it is fixed by
the arithmetic Frobenius `σ`: `X(E) = X(Breve E)^σ`. -/
theorem range_ofId_comp (A : Type*) [Semiring A] [Algebra E A] :
    Set.range (fun x : A →ₐ[E] E ↦ (Algebra.ofId E (Breve E)).comp x) =
      {x : A →ₐ[E] Breve E | (frobenius E : Breve E →ₐ[E] Breve E).comp x = x} :=
  AlgHom.range_comp_left_eq_fixedPoints _ (algebraMap E (Breve E)).injective
    (fixedPoints_frobenius E)

-- The integral statements use `(integerFrobenius E).toAlgHom`: elaborating the coercion of
-- `integerFrobenius E` to `𝒪[Breve E] →ₐ[𝒪[E]] 𝒪[Breve E]` exceeds the default instance-search
-- budget.
/-- **Integral points are the Frobenius-fixed integral points.** For an affine `𝒪[E]`-scheme
`𝒳 = Spec A`, a point with values in `𝒪[Breve E]` comes from a point with values in `𝒪[E]` exactly
when it is fixed by the arithmetic Frobenius `σ`: `𝒳(𝒪[E]) = 𝒳(𝒪[Breve E])^σ`. -/
theorem range_ofId_comp_integer (A : Type*) [Semiring A] [Algebra 𝒪[E] A] :
    Set.range (fun x : A →ₐ[𝒪[E]] 𝒪[E] ↦ (Algebra.ofId 𝒪[E] 𝒪[Breve E]).comp x) =
      {x : A →ₐ[𝒪[E]] 𝒪[Breve E] | (integerFrobenius E).toAlgHom.comp x = x} :=
  AlgHom.range_comp_left_eq_fixedPoints _ Valuation.HasExtension.algebraMap_injective
    (fixedPoints_integerFrobenius E)

/-! ### Points of affine groups -/

/-- **Rational points of a group are the Frobenius-fixed points.** For an affine group
`G = Spec H` over `E`, the image of `G(E)` in `G(Breve E)` is the subgroup fixed by the
arithmetic Frobenius `mapValue σ`. -/
theorem range_mapValue_ofId (H : Type*) [Semiring H] [HopfAlgebra E H] :
    (mapValue (H := H) (Algebra.ofId E (Breve E))).range =
      fixedSubgroup (G := WithConv (H →ₐ[E] Breve E))
        (mapValue (frobenius E : Breve E →ₐ[E] Breve E)) :=
  SetLike.ext fun _ ↦
    mem_mrange_mapValue_iff_mapValue_eq (algebraMap E (Breve E)).injective
      (fixedPoints_frobenius E)

/-- **Integral points of a group are the Frobenius-fixed integral points.** For an affine group
`𝒢 = Spec H` over `𝒪[E]`, the image of `𝒢(𝒪[E])` in `𝒢(𝒪[Breve E])` is the subgroup fixed by the
arithmetic Frobenius. -/
theorem range_mapValue_ofId_integer (H : Type*) [Semiring H] [HopfAlgebra 𝒪[E] H] :
    (mapValue (H := H) (Algebra.ofId 𝒪[E] 𝒪[Breve E])).range =
      fixedSubgroup (G := WithConv (H →ₐ[𝒪[E]] 𝒪[Breve E]))
        (mapValue (integerFrobenius E).toAlgHom) :=
  SetLike.ext fun _ ↦
    mem_mrange_mapValue_iff_mapValue_eq Valuation.HasExtension.algebraMap_injective
      (fixedPoints_integerFrobenius E)

variable (H : Type*) [Semiring H] [HopfAlgebra E H]

/-- **`G(E) = G(Breve E)^σ` as topological groups.** For an affine group `G = Spec H` over `E`,
the inclusion `G(E) → G(Breve E)` is an isomorphism of topological groups onto the subgroup fixed
by the arithmetic Frobenius, for the point topologies. -/
noncomputable def rationalPointsContinuousMulEquiv :
    WithConv (H →ₐ[E] E) ≃ₜ*
      fixedSubgroup (G := WithConv (H →ₐ[E] Breve E))
        (mapValue (frobenius E : Breve E →ₐ[E] Breve E)) where
  toMulEquiv :=
    (MonoidHom.ofInjective (mapValue_injective (algebraMap E (Breve E)).injective)).trans
      (MulEquiv.subgroupCongr (range_mapValue_ofId E H))
  continuous_toFun :=
    (continuous_mapValue (isClosedEmbedding_algebraMap E).continuous).subtype_mk _
  continuous_invFun := by
    refine (isEmbedding_mapValue (H₁ := H) (ψ := Algebra.ofId E (Breve E))
      (isClosedEmbedding_algebraMap E).isEmbedding)
      |>.isInducing.continuous_iff.2 <| continuous_subtype_val.congr fun y ↦ ?_
    -- The inverse is `(MonoidHom.ofInjective _).symm` after `(MulEquiv.subgroupCongr _).symm`,
    -- and the latter does not change the underlying point.
    exact (MonoidHom.apply_ofInjective_symm (mapValue_injective (algebraMap E (Breve E)).injective)
      ((MulEquiv.subgroupCongr (range_mapValue_ofId E H)).symm y)).symm

/-- The isomorphism `rationalPointsContinuousMulEquiv` is the inclusion of `G(E)` into
`G(Breve E)`. -/
@[simp]
theorem coe_rationalPointsContinuousMulEquiv (x : WithConv (H →ₐ[E] E)) :
    (rationalPointsContinuousMulEquiv E H x : WithConv (H →ₐ[E] Breve E)) =
      mapValue (Algebra.ofId E (Breve E)) x :=
  (rfl)

/-- The inverse of `rationalPointsContinuousMulEquiv` sends a Frobenius-fixed point of
`G(Breve E)` to the point of `G(E)` whose values map to its values in `Breve E`. -/
@[simp]
theorem algebraMap_rationalPointsContinuousMulEquiv_symm_apply_apply
    (y : fixedSubgroup (G := WithConv (H →ₐ[E] Breve E))
      (mapValue (frobenius E : Breve E →ₐ[E] Breve E))) (h : H) :
    algebraMap E (Breve E) (((rationalPointsContinuousMulEquiv E H).symm y).ofConv h) =
      (y : WithConv (H →ₐ[E] Breve E)).ofConv h := by
  conv_rhs => rw [← (rationalPointsContinuousMulEquiv E H).apply_symm_apply y]
  rw [coe_rationalPointsContinuousMulEquiv, mapValue_apply, WithConv.ofConv_toConv,
    AlgHom.comp_apply, Algebra.ofId_apply]

end TauCeti.MaxUnramifiedCompletion
