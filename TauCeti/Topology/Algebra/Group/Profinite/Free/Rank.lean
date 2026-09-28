/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Rank
import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
import TauCeti.Topology.Algebra.ContinuousMulEquiv
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Topology.Instances.ZMod
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basis
public import TauCeti.Topology.Algebra.ContinuousZModDual
import TauCeti.Topology.Algebra.Group.Profinite.ProP.ContinuousDual
import TauCeti.Topology.Algebra.Group.Profinite.ProP.DualRank
import TauCeti.Topology.Algebra.Group.Profinite.Hopfian

/-!
# The generator rank of a free pro-`p` group

The canonical generators of `freeProP p X` generate it topologically
(`freeProP.topologicalClosure_closure_range_of_eq_top`), so for finite `X` the free pro-`p` group
is topologically finitely generated (`isTopologicallyFinitelyGenerated_freeProP`). In the Frattini
quotient `freeProP p X ⧸ proPFrattini p (freeProP p X)`, an `𝔽_p`-vector space, the classes of
the generators are linearly independent: any assignment of exponents modulo `p` to the generators
is realised by a continuous character of the free pro-`p` group, through its universal property.
For finite `X` the classes also span, by Burnside's basis theorem, so they form a basis indexed by
`X`. The Frattini quotient is therefore `𝔽_p^X`, and the topological generator rank of
`freeProP p X` is the cardinality of `X`, in natural-number and in cardinal form.

For `X` of any cardinality the universal property identifies the continuous `𝔽_p`-valued
characters of `freeProP p X` with the arbitrary functions `X → 𝔽_p`
(`freeProP.continuousZModDualEquiv`), so by Burnside's basis theorem in cardinal form the
topological generator rank is the `𝔽_p`-dimension of `𝔽_p^X`. For finite `X` this is `#X` again;
for infinite `X` the Erdős–Kaplansky theorem gives the dimension `p ^ #X`, which is strictly
larger than `#X` (Ribes–Zalesskii, Section 3.3). This is why the free objects of infinite rank,
whose bases converge to `1`, are indexed by a profinite space rather than by a discrete type.

For finite `X` the continuous `𝔽_p`-dual has the basis dual to the generators
(`freeProP.dualBasis`), and the automorphisms of `freeProP p X` act on it through their
transposes. A family of elements whose classes span the Frattini quotient is the image of the
generators under a continuous automorphism (Burnside's basis theorem and the Hopf property of
topologically finitely generated profinite groups), and every linear automorphism of the
continuous dual is the transpose of a continuous automorphism of `freeProP p X`.

## Main definitions

* `TauCeti.freeProP.frattiniQuotientBasis`: for finite `X`, the basis of the Frattini quotient of
  `freeProP p X` formed by the classes of the generators.
* `TauCeti.freeProP.characterOfFun`: the continuous `𝔽_p`-valued character of `freeProP p X` with
  prescribed values on the generators.
* `TauCeti.freeProP.continuousZModDualEquiv`: the continuous `𝔽_p`-dual of `freeProP p X` is
  `𝔽_p^X`.
* `TauCeti.freeProP.dualBasis`: for finite `X`, the basis of the continuous `𝔽_p`-dual of
  `freeProP p X` dual to the generators.
* `TauCeti.freeProP.continuousMulEquivOfTopologicallyGenerates`: for finite `X`, the continuous
  automorphism of `freeProP p X` sending the generators to a given topological generating family.

## Main results

* `TauCeti.freeProP.linearIndependent_frattiniQuotient_of`: for every `X`, the classes of the
  generators in the Frattini quotient are linearly independent over `𝔽_p`.
* `TauCeti.freeProP.finrank_quotient_proPFrattini`: for finite `X`, the Frattini quotient has
  `𝔽_p`-dimension `Nat.card X`.
* `TauCeti.topologicalGeneratorRankNat_freeProP`, `TauCeti.topologicalGeneratorRank_freeProP`:
  for finite `X`, the free pro-`p` group on `X` has topological generator rank `Nat.card X`.
* `TauCeti.topologicalGeneratorRank_freeProP_eq_rank`: for every `X`, the topological generator
  rank of `freeProP p X` is the `𝔽_p`-dimension of `𝔽_p^X`.
* `TauCeti.topologicalGeneratorRank_freeProP_of_infinite`,
  `TauCeti.mk_lt_topologicalGeneratorRank_freeProP`: for infinite `X`, the rank is `p ^ #X`, which
  exceeds `#X`.
* `TauCeti.freeProP.exists_continuousMulEquiv_continuousZModDualMap_eq`: for finite `X`, every
  linear automorphism of the continuous `𝔽_p`-dual of `freeProP p X` is the transpose of a
  continuous automorphism.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Sections 2.8 and 3.3.
-/

public section

namespace TauCeti

open scoped Cardinal

universe u

variable (p : ℕ) {X : Type u}

namespace freeProP

variable [Fact p.Prime] (X)

/-- The continuous character of the free pro-`p` group on `X` with values in `𝔽_p^X` that reads
off the exponent of each generator modulo `p`: it sends the generator at `x` to the indicator
function of `x`. -/
private noncomputable def toPiZMod [DecidableEq X] :
    freeProP p X →ₜ* Multiplicative (X → ZMod p) :=
  lift (ZModModule.isPGroup_multiplicative (n := p) (G := X → ZMod p)).isProP fun x ↦
    Multiplicative.ofAdd (Pi.single x 1)

/-- The exponent-reading character kills the Frattini subgroup, because each of its coordinates
is a continuous character into a group of order `p`. -/
private theorem proPFrattini_le_ker_toPiZMod [DecidableEq X] :
    proPFrattini p (freeProP p X) ≤ (toPiZMod p X).ker := by
  intro g hg
  refine MonoidHom.mem_ker.mpr (Multiplicative.toAdd.injective (funext fun x₀ ↦ ?_))
  let ev : Multiplicative (X → ZMod p) →ₜ* Multiplicative (ZMod p) :=
    { toMonoidHom := (Pi.evalAddMonoidHom (fun _ : X ↦ ZMod p) x₀).toMultiplicative
      continuous_toFun := continuous_ofAdd.comp ((continuous_apply x₀).comp continuous_toAdd) }
  have hev (y : Multiplicative (X → ZMod p)) : ev y = Multiplicative.ofAdd (y.toAdd x₀) := rfl
  have h := MonoidHom.mem_ker.mp
    (proPFrattini_le_ker (H := Multiplicative (ZMod p)) (by simp) (ev.comp (toPiZMod p X)) hg)
  simpa [hev] using h

/-- The `𝔽_p`-linear map from the Frattini quotient of the free pro-`p` group on `X` to `𝔽_p^X`
induced by the exponent-reading character. -/
private noncomputable def frattiniQuotientToPi [DecidableEq X] :
    Additive (freeProP p X ⧸ proPFrattini p (freeProP p X)) →ₗ[ZMod p] (X → ZMod p) :=
  ((QuotientGroup.lift (proPFrattini p (freeProP p X)) (toPiZMod p X).toMonoidHom
    (proPFrattini_le_ker_toPiZMod p X)).toAdditiveLeft).toZModLinearMap p

private theorem frattiniQuotientToPi_of [DecidableEq X] (x : X) :
    frattiniQuotientToPi p X
      (Additive.ofMul ((of x : freeProP p X) : freeProP p X ⧸ proPFrattini p (freeProP p X))) =
        Pi.single x 1 := by
  simp [frattiniQuotientToPi, toPiZMod]

/-- **The classes of the generators in the Frattini quotient are linearly independent** over
`𝔽_p`, for a generating type `X` of any cardinality. -/
theorem linearIndependent_frattiniQuotient_of :
    LinearIndependent (ZMod p) fun x : X ↦
      Additive.ofMul (QuotientGroup.mk' (proPFrattini p (freeProP p X)) (of x)) := by
  classical
  refine LinearIndependent.of_comp (frattiniQuotientToPi p X) ?_
  simpa [Function.comp_def, frattiniQuotientToPi_of] using
    Pi.linearIndependent_single_one X (ZMod p)

/-! ### Continuous characters of a free pro-`p` group -/

/-- The continuous `𝔽_p`-valued character of the free pro-`p` group on `X` taking the value `f x`
at the generator `x`, for an arbitrary function `f : X → ZMod p`: the universal property applied
to the finite `p`-group `ℤ/p`, lifted to the universe of `X`. -/
noncomputable def characterOfFun (f : X → ZMod p) : freeProP p X →ₜ* Multiplicative (ZMod p) :=
  ((ContinuousMulEquiv.ulift : ULift.{u} (Multiplicative (ZMod p)) ≃ₜ* Multiplicative (ZMod p)) :
      ULift.{u} (Multiplicative (ZMod p)) →ₜ* Multiplicative (ZMod p)).comp
    (lift ((ZModModule.isPGroup_multiplicative (n := p) (G := ZMod p)).isProP.of_equiv
        ContinuousMulEquiv.ulift.symm)
      fun x ↦ ULift.up (Multiplicative.ofAdd (f x)))

/-- The character attached to `f` takes the value `f x` at the generator `x`. -/
@[simp]
theorem characterOfFun_of (f : X → ZMod p) (x : X) :
    characterOfFun p X f (of x) = Multiplicative.ofAdd (f x) := by
  simp [characterOfFun]

/-- Evaluation of a continuous `𝔽_p`-valued character at the generators, as an additive map. -/
private noncomputable def evalOfAddMonoidHom :
    continuousZModDual p (freeProP p X) →+ (X → ZMod p) where
  toFun φ x := Multiplicative.toAdd (Additive.toMul φ (of x))
  map_zero' := funext fun x ↦ by simp
  map_add' φ ψ := funext fun x ↦ by simp [toMul_add]

/-- **The continuous `𝔽_p`-dual of a free pro-`p` group is `𝔽_p^X`.** Evaluation at the generators
identifies the continuous characters of `freeProP p X` with the arbitrary functions `X → 𝔽_p`, as
`𝔽_p`-vector spaces; the inverse is `TauCeti.freeProP.characterOfFun`. No finiteness of `X` is
needed. -/
noncomputable def continuousZModDualEquiv :
    continuousZModDual p (freeProP p X) ≃ₗ[ZMod p] (X → ZMod p) where
  toFun := evalOfAddMonoidHom p X
  map_add' := map_add _
  map_smul' := ZMod.map_smul _
  invFun f := Additive.ofMul (characterOfFun p X f)
  left_inv φ := Additive.toMul.injective <| hom_ext fun x ↦ by simp [evalOfAddMonoidHom]
  right_inv f := funext fun x ↦ by simp [evalOfAddMonoidHom]

@[simp]
theorem continuousZModDualEquiv_apply (φ : continuousZModDual p (freeProP p X)) (x : X) :
    continuousZModDualEquiv p X φ x = Multiplicative.toAdd (Additive.toMul φ (of x)) :=
  (rfl)

@[simp]
theorem continuousZModDualEquiv_symm_apply (f : X → ZMod p) :
    (continuousZModDualEquiv p X).symm f = Additive.ofMul (characterOfFun p X f) :=
  (rfl)

/-! ### Finite rank -/

variable [Finite X]

/-- **The Frattini quotient of a free pro-`p` group of finite rank is `𝔽_p^X`.** For finite `X`
the classes of the generators form a basis of the Frattini quotient of `freeProP p X`, indexed
by `X`. -/
noncomputable def frattiniQuotientBasis :
    Module.Basis X (ZMod p) (Additive (freeProP p X ⧸ proPFrattini p (freeProP p X))) :=
  Module.Basis.mk (linearIndependent_frattiniQuotient_of p X) <| by
    have := (isTopologicallyFinitelyGenerated_freeProP p X).finite_quotient_proPFrattini p
    have hspan := (topologicallyGenerates_iff_frattiniQuotient_span_eq_top (isProP_freeProP p X)
      (Set.range (of : X → freeProP p X))).mp (topologicalClosure_closure_range_of_eq_top p X)
    rw [← Set.range_comp] at hspan
    exact hspan.ge

/-- The basis vector of the Frattini quotient at `x` is the class of the generator at `x`. -/
@[simp]
theorem frattiniQuotientBasis_apply (x : X) :
    frattiniQuotientBasis p X x =
      Additive.ofMul (QuotientGroup.mk' (proPFrattini p (freeProP p X)) (of x)) :=
  Module.Basis.mk_apply _ _ x

/-- The Frattini quotient of the free pro-`p` group on a finite type `X` has dimension
`Nat.card X` over `𝔽_p`. -/
@[simp]
theorem finrank_quotient_proPFrattini :
    Module.finrank (ZMod p) (Additive (freeProP p X ⧸ proPFrattini p (freeProP p X))) =
      Nat.card X :=
  Module.finrank_eq_nat_card_basis (frattiniQuotientBasis p X)

/-! ### The dual basis of the generators -/

section DualBasis

/-- **The dual basis of the generators**: the basis of the continuous `𝔽_p`-dual of `freeProP p X`
whose `i`-th vector is the coordinate character `x_j ↦ δ_{ij}`. -/
noncomputable def dualBasis : Module.Basis X (ZMod p) (continuousZModDual p (freeProP p X)) :=
  (Pi.basisFun (ZMod p) X).map (continuousZModDualEquiv p X).symm

/-- The `i`-th vector of the dual basis is the character reading off the exponent of `x_i`. -/
theorem dualBasis_apply [DecidableEq X] (i : X) :
    dualBasis p X i = Additive.ofMul (characterOfFun p X (Pi.single i 1)) := by
  rw [dualBasis, Module.Basis.map_apply, Pi.basisFun_apply, continuousZModDualEquiv_symm_apply]

/-- The `i`-th coordinate character takes the value `δ_{ij}` at the generator `x_j`. -/
@[simp]
theorem toMul_dualBasis_of [DecidableEq X] (i j : X) :
    (dualBasis p X i).toMul (of j) = Multiplicative.ofAdd ((Pi.single i 1 : X → ZMod p) j) := by
  rw [dualBasis_apply, toMul_ofMul, characterOfFun_of]

/-- The `i`-th coordinate of a character in the dual basis is its value at the generator `x_i`. -/
@[simp]
theorem dualBasis_repr (χ : continuousZModDual p (freeProP p X)) (i : X) :
    (dualBasis p X).repr χ i = (χ.toMul (of i)).toAdd := by
  rw [dualBasis, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
    Pi.basisFun_repr, continuousZModDualEquiv_apply]

end DualBasis

/-! ### Automorphisms of a free pro-`p` group of finite rank -/

section Automorphism

variable {p X}

/-- **The automorphism of a free pro-`p` group of finite rank sending the generators to a
topological generating family.** The endomorphism `x_i ↦ y_i` is surjective because the `y_i`
generate topologically, hence bijective by the Hopf property of topologically finitely generated
profinite groups. -/
noncomputable def continuousMulEquivOfTopologicallyGenerates (y : X → freeProP p X)
    (hy : (Subgroup.closure (Set.range y)).topologicalClosure = ⊤) :
    freeProP p X ≃ₜ* freeProP p X :=
  (isTopologicallyFinitelyGenerated_freeProP p X).continuousMulEquivOfSurjective
    (f := (lift (isProP_freeProP p X) y).toMonoidHom) (lift (isProP_freeProP p X) y).continuous
    (lift_surjective _ (by
      rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hy, Subgroup.coe_top]))

omit [Fact p.Prime] in
/-- The automorphism attached to a topological generating family sends the generators to it. -/
@[simp]
theorem continuousMulEquivOfTopologicallyGenerates_of (y : X → freeProP p X)
    (hy : (Subgroup.closure (Set.range y)).topologicalClosure = ⊤) (i : X) :
    continuousMulEquivOfTopologicallyGenerates y hy (of i) = y i := by
  rw [continuousMulEquivOfTopologicallyGenerates,
    IsTopologicallyFinitelyGenerated.continuousMulEquivOfSurjective_apply]
  exact lift_of _ _ i

/-- **Every linear automorphism of the continuous `𝔽_p`-dual of a free pro-`p` group of finite
rank is the transpose of a continuous automorphism.** Given `S`, a dual family `y` of the basis
`S⁻¹ χ_i`, where `χ_i` is the dual basis of the generators, satisfies `χ (y_j) = (S χ)(x_j)` for
every character `χ`; it generates topologically, by Burnside's basis theorem, and the automorphism
`x_j ↦ y_j` has transpose `S`. -/
theorem exists_continuousMulEquiv_continuousZModDualMap_eq
    (S : continuousZModDual p (freeProP p X) ≃ₗ[ZMod p] continuousZModDual p (freeProP p X)) :
    ∃ e : freeProP p X ≃ₜ* freeProP p X, ∀ χ : continuousZModDual p (freeProP p X),
      (e : freeProP p X →ₜ* freeProP p X).continuousZModDualMap χ = S χ := by
  cases nonempty_fintype X
  obtain ⟨y, -, hgen, hcoord⟩ :=
    (isProP_freeProP p X).exists_tendsto_cofinite_topologicallyGenerates_coord_eq
      ((dualBasis p X).map S.symm)
  -- Every character takes the same value at `y_j` as its image under `S` takes at `x_j`.
  have key (χ : continuousZModDual p (freeProP p X)) (j : X) :
      χ.toMul (y j) = (S χ).toMul (of j) := by
    have h := hcoord j χ
    rw [Module.Basis.coord_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_symm, dualBasis_repr] at h
    exact Multiplicative.toAdd.injective h.symm
  refine ⟨continuousMulEquivOfTopologicallyGenerates y hgen, fun χ ↦ ?_⟩
  refine Additive.toMul.injective (hom_ext fun j ↦ ?_)
  rw [ContinuousMonoidHom.toMul_continuousZModDualMap_apply, ContinuousMonoidHom.coe_coe,
    continuousMulEquivOfTopologicallyGenerates_of, key]

end Automorphism

end freeProP

variable [Fact p.Prime]

/-- **The rank of a free pro-`p` group is the dimension of `𝔽_p^X`**, for a generating type `X` of
any cardinality: Burnside's basis theorem in cardinal form, read through the continuous dual
`TauCeti.freeProP.continuousZModDualEquiv`. -/
theorem topologicalGeneratorRank_freeProP_eq_rank :
    topologicalGeneratorRank (freeProP p X) = Module.rank (ZMod p) (X → ZMod p) := by
  rw [(isProP_freeProP p X).topologicalGeneratorRank_eq_rank_continuousZModDual,
    (freeProP.continuousZModDualEquiv p X).rank_eq]

/-- **The free pro-`p` group on an infinite type `X` has rank `p ^ #X`.** The continuous dual is
`𝔽_p^X`, whose dimension over `𝔽_p` is its cardinality by the Erdős–Kaplansky theorem. -/
theorem topologicalGeneratorRank_freeProP_of_infinite [Infinite X] :
    topologicalGeneratorRank (freeProP p X) = (p : Cardinal.{u}) ^ #X := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [topologicalGeneratorRank_freeProP_eq_rank, rank_fun_infinite, Cardinal.mk_arrow,
    Cardinal.lift_uzero, Cardinal.mk_fintype, ZMod.card, Cardinal.lift_natCast]

/-- **An infinite type is strictly smaller than the rank of the free pro-`p` group on it**: the
rank is `p ^ #X`, not `#X`. -/
theorem mk_lt_topologicalGeneratorRank_freeProP [Infinite X] :
    #X < topologicalGeneratorRank (freeProP p X) := by
  rw [topologicalGeneratorRank_freeProP_of_infinite]
  exact Cardinal.cantor' #X (by exact_mod_cast (Fact.out : p.Prime).one_lt)

variable [Finite X]

/-- **The free pro-`p` group on a finite type `X` has topological generator rank `Nat.card X`**,
in natural-number form. -/
@[simp]
theorem topologicalGeneratorRankNat_freeProP (h : IsTopologicallyFinitelyGenerated (freeProP p X)) :
    topologicalGeneratorRankNat (freeProP p X) h = Nat.card X := by
  rw [(isProP_freeProP p X).topologicalGeneratorRankNat_eq_finrank_quotient_proPFrattini h,
    freeProP.finrank_quotient_proPFrattini]

/-- **The free pro-`p` group on a finite type `X` has topological generator rank `#X`**, in
cardinal form. -/
@[simp]
theorem topologicalGeneratorRank_freeProP : topologicalGeneratorRank (freeProP p X) = #X := by
  rw [← topologicalGeneratorRankNat_eq_topologicalGeneratorRank
    (isTopologicallyFinitelyGenerated_freeProP p X), topologicalGeneratorRankNat_freeProP,
    Nat.cast_card]

end TauCeti
