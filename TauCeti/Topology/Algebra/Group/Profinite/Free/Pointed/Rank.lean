/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Pointed.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Rank
public import TauCeti.Topology.Compactification.OnePoint.Finsupp
public import TauCeti.Topology.ContinuousMap.Algebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Topology.Algebra.ContinuousMulEquiv
import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank

/-!
# The rank of the free pro-`p` group on a pointed space

Let `(X, x₀)` be a pointed topological space and `F = F_p(X, x₀)` the free pro-`p` group on it,
the free pro-`C` group `freeProCPointed (finiteGroupClassP p) x₀` for `C` the class of finite
`p`-groups. By the universal property, a continuous `𝔽_p`-valued character of `F` is the same as a
continuous map `X → 𝔽_p` vanishing at `x₀`, so the continuous `𝔽_p`-dual of `F` is the space of
such maps (`TauCeti.freeProCPointed.continuousZModDualEquiv`), and Burnside's basis theorem in
cardinal form gives the rank of `F` as the `𝔽_p`-dimension of that space
(`TauCeti.freeProCPointed.topologicalGeneratorRank_eq_rank`).

For the one-point compactification `S⁺` of a discrete space `S`, pointed at `∞`, the continuous
maps `S⁺ → 𝔽_p` vanishing at `∞` are the finitely supported functions on `S`, so the rank of
`F_p(S⁺, ∞)` is `#S` (`TauCeti.freeProCPointed.topologicalGeneratorRank_onePoint`). The free
pro-`p` group on the type `S`, whose universal property quantifies over all maps `S → P`, has rank
`p ^ #S` instead when `S` is infinite (`TauCeti.topologicalGeneratorRank_freeProP_of_infinite`).
Since a topological isomorphism preserves the rank, the continuous surjection
`freeProC C S → F_C(S⁺, ∞)` induced by `S → S⁺` is therefore **not injective** for infinite discrete
`S` at `C` the class of finite `p`-groups (`TauCeti.freeProCPointed.not_injective_fromFreeProC`):
the two candidate "free pro-`p` groups on an infinite set" are different groups, and the one with
a basis converging to `1` is the proper quotient.

## Main definitions

* `TauCeti.freeProCPointed.characterOfContinuousMap`: the continuous `𝔽_p`-valued character of
  `F_p(X, x₀)` extending a continuous map `X → 𝔽_p` that vanishes at `x₀`.
* `TauCeti.freeProCPointed.continuousZModDualEquiv`: the continuous `𝔽_p`-dual of `F_p(X, x₀)` is
  the space of continuous maps `X → 𝔽_p` vanishing at `x₀`.

## Main results

* `TauCeti.freeProCPointed.topologicalGeneratorRank_eq_rank`: the rank of `F_p(X, x₀)` is the
  `𝔽_p`-dimension of the continuous maps `X → 𝔽_p` vanishing at `x₀`.
* `TauCeti.freeProCPointed.topologicalGeneratorRank_onePoint`: the rank of `F_p(S⁺, ∞)` is `#S`
  for a discrete space `S`.
* `TauCeti.freeProCPointed.not_injective_fromFreeProC`: for an infinite discrete `S`, the surjection
  from the free pro-`p` group on the type `S` onto `F_p(S⁺, ∞)` is not injective.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, 2nd ed., Section 3.3.
-/

public section

open scoped Cardinal OnePoint

namespace TauCeti

universe u

namespace freeProCPointed

variable (p : ℕ) [Fact p.Prime] {X : Type u} [TopologicalSpace X] (x₀ : X)

/-! ### Continuous characters -/

omit [Fact p.Prime] in
/-- The free pro-`C` group on a pointed space, for `C` the class of finite `p`-groups, is
pro-`p`. -/
theorem isProP_finiteGroupClassP : IsProP p (freeProCPointed (finiteGroupClassP.{u} p) x₀) :=
  isProC_finiteGroupClassP_iff.mp (isProC_freeProCPointed (finiteGroupClassP.{u} p) x₀)

/-- The continuous `𝔽_p`-valued character of the free pro-`p` group on `(X, x₀)` extending a
continuous map `f : X → 𝔽_p` with `f x₀ = 0`: the universal property applied to the finite `p`-group
`ℤ/p`, lifted to the universe of `X`. -/
noncomputable def characterOfContinuousMap (f : C(X, ZMod p)) (hf : f x₀ = 0) :
    freeProCPointed (finiteGroupClassP.{u} p) x₀ →ₜ* Multiplicative (ZMod p) :=
  ((ContinuousMulEquiv.ulift : ULift.{u} (Multiplicative (ZMod p)) ≃ₜ* Multiplicative (ZMod p)) :
      ULift.{u} (Multiplicative (ZMod p)) →ₜ* Multiplicative (ZMod p)).comp
    (lift (isProC_finiteGroupClassP_iff.mpr
        ((ZModModule.isPGroup_multiplicative (n := p) (G := ZMod p)).isProP.of_equiv
          ContinuousMulEquiv.ulift.symm))
      (fun x ↦ ULift.up (Multiplicative.ofAdd (f x)))
      (continuous_uliftUp.comp (continuous_ofAdd.comp f.continuous)) (ULift.ext _ _ (by simp [hf])))

/-- The character extending `f` takes the value `f x` at the image of `x`. -/
@[simp]
theorem characterOfContinuousMap_of (f : C(X, ZMod p)) (hf : f x₀ = 0) (x : X) :
    characterOfContinuousMap p x₀ f hf (of (finiteGroupClassP.{u} p) x₀ x) =
      Multiplicative.ofAdd (f x) := by
  simp [characterOfContinuousMap]

/-- Restriction of a continuous character to the image of `X`, as an additive map into the
continuous maps `X → 𝔽_p` vanishing at `x₀`. -/
private noncomputable def restrictAddMonoidHom :
    continuousZModDual p (freeProCPointed (finiteGroupClassP.{u} p) x₀) →+
      (ContinuousMap.evalCLM (ZMod p) x₀ : C(X, ZMod p) →L[ZMod p] ZMod p).ker where
  toFun φ := ⟨⟨fun x ↦ Multiplicative.toAdd
      (Additive.toMul φ (of (finiteGroupClassP.{u} p) x₀ x)),
      continuous_toAdd.comp ((Additive.toMul φ).continuous.comp (continuous_of _ x₀))⟩,
    by simp [LinearMap.mem_ker, of_basePoint]⟩
  map_zero' := Subtype.ext <| ContinuousMap.ext fun x ↦ by simp
  map_add' φ ψ := Subtype.ext <| ContinuousMap.ext fun x ↦ by simp [toMul_add]

/-- **The continuous `𝔽_p`-dual of the free pro-`p` group on a pointed space** is the space of
continuous maps `X → 𝔽_p` vanishing at the base point, by restriction to the image of `X`; the
inverse is `TauCeti.freeProCPointed.characterOfContinuousMap`. -/
noncomputable def continuousZModDualEquiv :
    continuousZModDual p (freeProCPointed (finiteGroupClassP.{u} p) x₀) ≃ₗ[ZMod p]
      (ContinuousMap.evalCLM (ZMod p) x₀ : C(X, ZMod p) →L[ZMod p] ZMod p).ker where
  toFun := restrictAddMonoidHom p x₀
  map_add' := map_add _
  map_smul' := ZMod.map_smul _
  invFun f := Additive.ofMul (characterOfContinuousMap p x₀ f.1
      (ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM (ZMod p) (ZMod p) x₀ f))
  left_inv φ := Additive.toMul.injective <| hom_ext fun x ↦ by simp [restrictAddMonoidHom]
  right_inv f := Subtype.ext <| ContinuousMap.ext fun x ↦ by simp [restrictAddMonoidHom]

@[simp]
theorem coe_continuousZModDualEquiv_apply_apply
    (φ : continuousZModDual p (freeProCPointed (finiteGroupClassP.{u} p) x₀)) (x : X) :
    (continuousZModDualEquiv p x₀ φ : C(X, ZMod p)) x =
      Multiplicative.toAdd (Additive.toMul φ (of (finiteGroupClassP.{u} p) x₀ x)) :=
  (rfl)

@[simp]
theorem continuousZModDualEquiv_symm_apply
    (f : (ContinuousMap.evalCLM (ZMod p) x₀ : C(X, ZMod p) →L[ZMod p] ZMod p).ker) :
    (continuousZModDualEquiv p x₀).symm f =
      (Additive.ofMul (characterOfContinuousMap p x₀ f.1
      (ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM (ZMod p) (ZMod p) x₀ f)) :
        continuousZModDual p (freeProCPointed (finiteGroupClassP.{u} p) x₀)) :=
  (rfl)

/-! ### Rank -/

/-- **The rank of the free pro-`p` group on a pointed space** is the `𝔽_p`-dimension of the space
of continuous maps `X → 𝔽_p` vanishing at the base point: Burnside's basis theorem in cardinal
form, read through `TauCeti.freeProCPointed.continuousZModDualEquiv`. -/
theorem topologicalGeneratorRank_eq_rank :
    topologicalGeneratorRank (freeProCPointed (finiteGroupClassP.{u} p) x₀) =
      Module.rank (ZMod p)
        (ContinuousMap.evalCLM (ZMod p) x₀ : C(X, ZMod p) →L[ZMod p] ZMod p).ker := by
  rw [(isProP_finiteGroupClassP p x₀).topologicalGeneratorRank_eq_rank_continuousZModDual,
    (continuousZModDualEquiv p x₀).rank_eq]

variable (S : Type u) [TopologicalSpace S] [DiscreteTopology S]

/-- **The rank of the free pro-`p` group on the pointed one-point compactification of a discrete
space `S` is `#S`**: the continuous maps `S⁺ → 𝔽_p` vanishing at `∞` are the finitely supported
functions on `S`. -/
theorem topologicalGeneratorRank_onePoint :
    topologicalGeneratorRank (freeProCPointed (finiteGroupClassP.{u} p) (∞ : OnePoint S)) = #S := by
  rw [topologicalGeneratorRank_eq_rank,
    ← (OnePoint.finsuppLinearEquivKerEvalInfty S (ZMod p) (ZMod p)).rank_eq, rank_finsupp_self,
    Cardinal.lift_uzero]

/-- **The canonical surjection from the free pro-`p` group on an infinite type onto the free pro-`p`
group on its pointed one-point compactification is not injective.** For an infinite discrete space
`S`, the continuous surjection `freeProC C S → F_C(S⁺, ∞)` induced by `S → S⁺` is not injective when
`C` is the class of finite `p`-groups: an injective continuous surjection between profinite groups
is a topological isomorphism, which would force the ranks `p ^ #S` of the source and `#S` of the
target to agree. -/
theorem not_injective_fromFreeProC [Infinite S] :
    ¬ Function.Injective (fromFreeProC (finiteGroupClassP.{u} p) S) := by
  intro hinj
  have hb : Function.Bijective (fromFreeProC (finiteGroupClassP.{u} p) S) :=
    ⟨hinj, fromFreeProC_surjective _ S⟩
  let e : freeProC (finiteGroupClassP.{u} p) S ≃ₜ*
      freeProCPointed (finiteGroupClassP.{u} p) (∞ : OnePoint S) :=
    (MulEquiv.ofBijective _ hb).toContinuousMulEquiv fun s ↦
      ((fromFreeProC (finiteGroupClassP.{u} p) S).continuous.homeoOfEquivCompactToT2
        (f := (MulEquiv.ofBijective _ hb).toEquiv)).isOpen_preimage
  have h := mk_lt_topologicalGeneratorRank_freeProP p (X := S)
  rw [← topologicalGeneratorRank_congr (freeProC.equivFreeProP p S),
    topologicalGeneratorRank_congr e, topologicalGeneratorRank_onePoint] at h
  exact lt_irrefl _ h

end freeProCPointed

end TauCeti
