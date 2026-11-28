/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CharacterValue
public import TauCeti.Algebra.AlgebraicGroup.MultiplicativeGroup.Basic
public import TauCeti.NumberTheory.NumberField.Global.AdelicPoints.Basic
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.Topology.Instances.NNReal

/-!
# The norm-one subgroup of the adelic points

Let `K` be a number field and `G = Spec H` an affine group scheme over `K`, given by a Hopf
algebra `H`. A rational character `χ` of `G`, a group-like element of `H`, has a value
`χ(x) ∈ 𝔸_K^×` at every adelic point `x ∈ G(𝔸_K)` (`GroupLike.characterValue`), and so an idele
norm `‖χ(x)‖`. The **norm-one subgroup**
```
G(𝔸_K)^1 = {x ∈ G(𝔸_K) | ‖χ(x)‖ = 1 for every rational character χ of G}
```
is the intersection of the kernels of the homomorphisms `x ↦ ‖χ(x)‖`. It is the subgroup on
which automorphic quotients of finite volume are formed: for connected `G` the quotient
`G(K)\G(𝔸_K)^1` has finite volume, while `G(K)\G(𝔸_K)` has infinite volume as soon as `G` has a
nontrivial rational character.

This file proves the basic structure of `G(𝔸_K)^1`. It is a closed normal subgroup, because each
`x ↦ ‖χ(x)‖` is a continuous homomorphism to the positive reals. It contains the rational points
`G(K)`, by the product formula. It contains every compact subgroup, because the positive reals
have no nontrivial compact subgroup, and the commutator subgroup, because the positive reals are
commutative. When `G` has no nontrivial rational character it is all of `G(𝔸_K)`. For the
multiplicative group `𝔾ₘ`, whose adelic points are the ideles, it is the kernel of the idele
norm, since the rational characters of `𝔾ₘ` are the powers of the coordinate `T`.

The norm-one subgroup is not the product of a norm-one archimedean part with the finite adelic
points: an idele of norm one can have archimedean component of absolute value other than one, as
the principal idele `2` of `ℚ` shows (`TauCeti.AdelicNormOne.norm_diagonal_two_infinite`).

## Main declarations

* `TauCeti.AdelicPoints.normOne`: the norm-one subgroup `G(𝔸_K)^1`, with
  `TauCeti.AdelicPoints.mem_normOne_iff`.
* `TauCeti.AdelicPoints.isClosed_normOne`, `TauCeti.AdelicPoints.normOne_normal`: it is a closed
  normal subgroup.
* `TauCeti.AdelicPoints.range_diagonal_le_normOne`: it contains the rational points.
* `TauCeti.AdelicPoints.le_normOne_of_isCompact`: it contains every compact subgroup.
* `TauCeti.AdelicPoints.commutator_le_normOne`: it contains the commutator subgroup.
* `TauCeti.AdelicPoints.normOne_eq_top`: it is everything when there is no nontrivial rational
  character.
* `TauCeti.AdelicPoints.normOne_laurentPolynomial`: for `𝔾ₘ` it is the kernel of the idele norm.

## References

* J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4 (2005), §3, p. 16.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), §5.8, p. 22.
-/

public section

open IsDedekindDomain NumberField
open scoped NNReal LaurentPolynomial

namespace TauCeti.AdelicPoints

open GlobalNumberFields

variable (K H : Type*) [Field K] [NumberField K] [Semiring H] [HopfAlgebra K H]

/-- The **norm-one subgroup** `G(𝔸_K)^1` of the adelic points of `G = Spec H`: the adelic points
`x` at which every rational character `χ` of `G` has value of idele norm `‖χ(x)‖ = 1`. -/
noncomputable def normOne : Subgroup (AdelicPoints (𝓞 K) K H) :=
  ⨅ χ : GroupLike K H, (ideleNorm.comp (χ.characterValue (AdeleRing (𝓞 K) K))).ker

variable {K H}

/-- An adelic point lies in the norm-one subgroup exactly when every rational character has value
of idele norm one there. -/
@[simp]
theorem mem_normOne_iff {x : AdelicPoints (𝓞 K) K H} :
    x ∈ normOne K H ↔ ∀ χ : GroupLike K H, ideleNorm (χ.characterValue _ x) = 1 := by
  simp [normOne]

variable (K H)

/-- The norm-one subgroup is normal. -/
instance normOne_normal : (normOne K H).Normal :=
  Subgroup.normal_iInf_normal fun _ ↦ MonoidHom.normal_ker _

/-- The norm-one subgroup is closed. -/
theorem isClosed_normOne : IsClosed (normOne K H : Set (AdelicPoints (𝓞 K) K H)) := by
  rw [normOne, Subgroup.coe_iInf]
  refine isClosed_iInter fun χ ↦ ?_
  exact isClosed_singleton.preimage <|
    continuous_ideleNorm.comp (χ.continuous_characterValue (A := AdeleRing (𝓞 K) K))

variable {K H}

/-- **Rational points have norm one.** The value of a rational character at a rational point is a
principal idele, of idele norm one by the product formula. -/
theorem diagonal_mem_normOne (g : WithConv (H →ₐ[K] K)) :
    diagonal (𝓞 K) K H g ∈ normOne K H := by
  rw [mem_normOne_iff]
  intro χ
  rw [diagonal_eq_mapValue, GroupLike.characterValue_mapValue]
  exact ideleNorm_unitEmbedding _

variable (K H)

/-- The norm-one subgroup contains the rational points. -/
theorem range_diagonal_le_normOne : (diagonal (𝓞 K) K H).range ≤ normOne K H := by
  rintro _ ⟨g, rfl⟩
  exact diagonal_mem_normOne g

variable {K H}

/-- **Compact subgroups have norm one.** Every compact subgroup of the adelic points lies in the
norm-one subgroup: its image under the continuous homomorphism `x ↦ ‖χ(x)‖` is a compact subgroup
of the positive reals, hence trivial. -/
theorem le_normOne_of_isCompact {U : Subgroup (AdelicPoints (𝓞 K) K H)}
    (hU : IsCompact (U : Set (AdelicPoints (𝓞 K) K H))) : U ≤ normOne K H := by
  intro x hx
  rw [mem_normOne_iff]
  intro χ
  refine Units.ext ?_
  exact ((Units.coeHom ℝ≥0).comp (ideleNorm.comp (χ.characterValue _))).eq_one_of_mem_of_isCompact
    (Units.continuous_val.comp (continuous_ideleNorm.comp χ.continuous_characterValue)) hU hx

variable (K H)

/-- The norm-one subgroup contains the commutator subgroup, since each idele norm `‖χ(x)‖` is a
homomorphism to a commutative group. -/
theorem commutator_le_normOne : commutator (AdelicPoints (𝓞 K) K H) ≤ normOne K H :=
  le_iInf fun _ ↦ Group.Abelianization.commutator_le_ker _

/-- **Groups without rational characters.** If the only rational character of `G` is the trivial
one, the norm-one subgroup is the whole group of adelic points. -/
theorem normOne_eq_top [Subsingleton (GroupLike K H)] : normOne K H = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ mem_normOne_iff.2 fun χ ↦ ?_
  rw [Subsingleton.elim χ 1, GroupLike.characterValue_one, map_one]

/-- **The norm-one subgroup of `𝔾ₘ`.** For the multiplicative group, whose adelic points are the
ideles through `TauCeti.MultiplicativeGroup.pointsMulEquiv`, the norm-one subgroup is the kernel
of the idele norm. Its rational characters are the powers `T n` of the coordinate, and
`‖x ^ n‖ = ‖x‖ ^ n`. -/
theorem normOne_laurentPolynomial :
    normOne K K[T;T⁻¹] =
      (ideleNorm (K := K)).ker.comap
        (MultiplicativeGroup.pointsMulEquiv (A := AdeleRing (𝓞 K) K)).toMonoidHom := by
  ext x
  rw [mem_normOne_iff, Subgroup.mem_comap, MonoidHom.mem_ker]
  -- The value of the coordinate character `T` is the idele attached to `x`.
  have hT : (MultiplicativeGroup.groupLikeT K).characterValue _ x =
      MultiplicativeGroup.pointsMulEquiv x :=
    Units.ext <| by simp
  refine ⟨fun h ↦ hT ▸ h _, fun h χ ↦ ?_⟩
  -- Every other rational character is a monomial `T n`, with value the `n`-th power.
  obtain ⟨n, hn⟩ :=
    LaurentPolynomial.isGroupLikeElem_iff_mem_range_T.1 χ.isGroupLikeElem_val
  have hχ : χ.characterValue _ x = MultiplicativeGroup.pointsMulEquiv x ^ n :=
    Units.ext <| by
      rw [GroupLike.val_characterValue, ← hn]
      exact AlgHom.apply_laurentPolynomial_T_of_apply_T_one (by simp) n
  rw [hχ, map_zpow]
  exact (congrArg (· ^ n) h).trans (one_zpow n)

end TauCeti.AdelicPoints
