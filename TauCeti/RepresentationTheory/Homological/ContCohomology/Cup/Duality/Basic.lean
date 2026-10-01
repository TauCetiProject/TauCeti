/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Instances.ZMod
public import TauCeti.Algebra.GroupAction.Trivial
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.RepresentationTheory.Homological.ContCohomology.H2ZMod
public import TauCeti.Topology.Algebra.GroupAction.InternalHom.Basic

/-!
# Evaluation cups for finite discrete modules

For a finite discrete `G`-module `M` and a discrete module `N`, evaluation is an equivariant
biadditive pairing from `InternalHom G M N` and `M` to `N`. The three low-degree cup shapes of
total degree two give pairings from `Hⁱ(G, InternalHom G M N)` and `H²⁻ⁱ(G, M)` to `H²(G, N)`.
These are the underlying cohomological pairings used in duality statements.

The cochain formulas below fix the order of the two inputs: the internal hom is always the first
factor, so in degree `(1,1)` the evaluation is `a(g) (g • b(h))`.

Read with the module first, the same cups give **Tate's duality maps**
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, InternalHom G M N), H²(G, N))`, `x ↦ ⟨x, -⟩`, for `i = 0, 1, 2`
(Serre, *Structure de certains pro-p-groupes*, §9.1): `TauCeti.ContCohomology.dualityMap0`,
`dualityMap1` and `dualityMap2`. They are the explicit cups along the opposite evaluation pairing
`(m, φ) ↦ φ m`, so graded commutativity relates them to the evaluation cups: `α₀` and `α₂` are the
`(2,0)` and `(0,2)` evaluation cups with their arguments swapped, and `α₁` is the negative of the
swapped `(1,1)` evaluation cup. For a trivial action on `ZMod n` the internal hom is `ZMod n` again,
by evaluation at `1`, and the duality maps are scalar multiplication on `H²(G, ZMod n)` in degrees
`0` and `2` and the cup product of multiplication in degree `1`. In that setting `α₂` is always
bijective, and `α₀` is bijective as soon as `H²(G, ZMod p)` is one-dimensional.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki
  exp. 252 (1963), §9.1.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN

section ZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Evaluation on `H⁰(G, InternalHom G M N) × H²(G, M)`. -/
noncomputable def explicitDualityPairing02 :
    H0 G (InternalHom G M N) →+ H2 G M →+ H2 G N :=
  explicitCup02 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- The `(0,2)` evaluation pairing is the explicit `(0,2)` cup along the evaluation pairing. -/
theorem explicitDualityPairing02_def :
    explicitDualityPairing02 G M N =
      explicitCup02 G (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) :=
  (rfl)

/-- On cocycles, the `(0,2)` evaluation cup evaluates the invariant homomorphism pointwise. -/
@[simp]
theorem explicitDualityPairing02_mk (a : H0 G (InternalHom G M N)) (b : Z2 G M) :
    explicitDualityPairing02 G M N a (b : H2 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G (a : InternalHom G M N) ((b : G × G → M) q),
        cup02_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b.2⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing02] using
    explicitCup02_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end ZeroTwo

section OneOneAndTwoZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Evaluation on `H¹(G, InternalHom G M N) × H¹(G, M)`. -/
noncomputable def explicitDualityPairing11 :
    H1 G (InternalHom G M N) →+ H1 G M →+ H2 G N :=
  explicitCup11 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- The `(1,1)` evaluation pairing is the explicit `(1,1)` cup along the evaluation pairing. -/
theorem explicitDualityPairing11_def :
    explicitDualityPairing11 G M N =
      explicitCup11 G (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) :=
  (rfl)

/-- Evaluation on `H²(G, InternalHom G M N) × H⁰(G, M)`. -/
noncomputable def explicitDualityPairing20 :
    H2 G (InternalHom G M N) →+ H0 G M →+ H2 G N :=
  explicitCup20 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- The `(2,0)` evaluation pairing is the explicit `(2,0)` cup along the evaluation pairing. -/
theorem explicitDualityPairing20_def :
    explicitDualityPairing20 G M N =
      explicitCup20 G (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) :=
  (rfl)

/-- On cocycles, the `(1,1)` evaluation cup applies the first cocycle to the translate of the
second. -/
@[simp]
theorem explicitDualityPairing11_mk (a : Z1 G (InternalHom G M N)) (b : Z1 G M) :
    explicitDualityPairing11 G M N (a : H1 G (InternalHom G M N)) (b : H1 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G → InternalHom G M N) q.1)
          (q.1 • (b : G → M) q.2),
        cup11_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b.2⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing11] using
    explicitCup11_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

/-- On cocycles, the `(2,0)` evaluation cup evaluates at an invariant element of `M`. -/
@[simp]
theorem explicitDualityPairing20_mk (a : Z2 G (InternalHom G M N)) (b : H0 G M) :
    explicitDualityPairing20 G M N (a : H2 G (InternalHom G M N)) b =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G × G → InternalHom G M N) q)
          ((q.1 * q.2) • (b : M)),
        cup20_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing20] using
    explicitCup20_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end OneOneAndTwoZero

section DualityMap

/-! ### Tate's duality maps

The evaluation cups with the module in the first slot. -/

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **Tate's duality map in degree `0`**,
`α₀ : H⁰(G, M) → Hom(H²(G, InternalHom G M N), H²(G, N))`: the `(0,2)` cup along the opposite
evaluation pairing, `α₀ m b = ⟨m, b⟩`, the class of the cocycle `(g, h) ↦ b (g, h) m`. -/
noncomputable def dualityMap0 : H0 G M →+ H2 G (InternalHom G M N) →+ H2 G N :=
  explicitCup02 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

/-- **Tate's duality map in degree `1`**,
`α₁ : H¹(G, M) → Hom(H¹(G, InternalHom G M N), H²(G, N))`: the `(1,1)` cup along the opposite
evaluation pairing, `α₁ a b = ⟨a, b⟩`, the class of the cocycle `(g, h) ↦ (g • b h) (a g)`. -/
noncomputable def dualityMap1 : H1 G M →+ H1 G (InternalHom G M N) →+ H2 G N :=
  explicitCup11 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

/-- On cocycles, `α₀` evaluates the cocycle at the invariant element. -/
@[simp]
theorem dualityMap0_mk (m : H0 G M) (b : Z2 G (InternalHom G M N)) :
    dualityMap0 G M N m (b : H2 G (InternalHom G M N)) =
      ((⟨fun q : G × G =>
          (InternalHom.evalPairing G).flip (m : M) ((b : G × G → InternalHom G M N) q),
        cup02_mem_Z2 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
          continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))
          m b.2⟩ : Z2 G N) : H2 G N) := by
  simpa only [dualityMap0] using
    explicitCup02_mk G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
      continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) m b

/-- On cocycles, `α₁` applies the translate of the second cocycle to the first. -/
@[simp]
theorem dualityMap1_mk (a : Z1 G M) (b : Z1 G (InternalHom G M N)) :
    dualityMap1 G M N (a : H1 G M) (b : H1 G (InternalHom G M N)) =
      ((⟨fun q : G × G => (InternalHom.evalPairing G).flip ((a : G → M) q.1)
          (q.1 • (b : G → InternalHom G M N) q.2),
        cup11_mem_Z2 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
          continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))
          a.2 b.2⟩ : Z2 G N) : H2 G N) := by
  simpa only [dualityMap1] using
    explicitCup11_mk G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
      continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) a b

/-- `α₀` is the `(2,0)` evaluation cup with its arguments swapped: graded commutativity in
bidegree `(0,2)`, where the sign is `1` (`explicitCup02_eq_cup20_flip` along the opposite
evaluation pairing). -/
theorem dualityMap0_eq_explicitDualityPairing20 (m : H0 G M) (b : H2 G (InternalHom G M N)) :
    dualityMap0 G M N m b = explicitDualityPairing20 G M N b m :=
  explicitCup02_eq_cup20_flip G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) m b

/-- `α₁` is the negative of the `(1,1)` evaluation cup with its arguments swapped: graded
commutativity in bidegree `(1,1)`, where the sign is `-1` (`explicitCup11_eq_neg_flip` along the
opposite evaluation pairing). -/
theorem dualityMap1_eq_neg_explicitDualityPairing11 (a : H1 G M)
    (b : H1 G (InternalHom G M N)) :
    dualityMap1 G M N a b = -explicitDualityPairing11 G M N b a :=
  explicitCup11_eq_neg_flip G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) a b

end DualityMap

section DualityMapTwo

/-! In degree `2` the internal hom sits in the degree-zero slot of the cup, whose continuity is
never used, so `α₂` needs neither continuous inversion on `G` nor finiteness of `M`. -/

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **Tate's duality map in degree `2`**,
`α₂ : H²(G, M) → Hom(H⁰(G, InternalHom G M N), H²(G, N))`: the `(2,0)` cup along the opposite
evaluation pairing, `α₂ b φ = ⟨b, φ⟩`, the class of the cocycle `(g, h) ↦ φ (b (g, h))` for an
invariant `φ`. -/
noncomputable def dualityMap2 : H2 G M →+ H0 G (InternalHom G M N) →+ H2 G N :=
  explicitCup20 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
    continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))

/-- On cocycles, `α₂` applies the translate of the invariant homomorphism to the cocycle. -/
@[simp]
theorem dualityMap2_mk (b : Z2 G M) (φ : H0 G (InternalHom G M N)) :
    dualityMap2 G M N (b : H2 G M) φ =
      ((⟨fun q : G × G => (InternalHom.evalPairing G).flip ((b : G × G → M) q)
          ((q.1 * q.2) • (φ : InternalHom G M N)),
        cup20_mem_Z2 G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
          continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G))
          b.2 φ⟩ : Z2 G N) : H2 G N) := by
  simpa only [dualityMap2] using
    explicitCup20_mk G M (InternalHom G M N) N (InternalHom.evalPairing G).flip
      continuous_of_discreteTopology (InternalHom.evalPairing_flip_equivariant (G := G)) b φ

/-- `α₂` is the `(0,2)` evaluation cup with its arguments swapped: graded commutativity in
bidegree `(2,0)`, where the sign is `1` (`explicitCup02_eq_cup20_flip` along the evaluation
pairing, read backwards). -/
theorem dualityMap2_eq_explicitDualityPairing02 (b : H2 G M) (φ : H0 G (InternalHom G M N)) :
    dualityMap2 G M N b φ = explicitDualityPairing02 G M N φ b :=
  (explicitCup02_eq_cup20_flip G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) φ b).symm

end DualityMapTwo

section TrivialZMod

/-! ### Trivial `ZMod n` coefficients

For a trivial action of `G` on `ZMod n` the conjugation action on the internal hom
`InternalHom G (ZMod n) (ZMod n)` is trivial too
(`TauCeti.InternalHom.smul_eq_self_of_smul_eq_self`), and evaluation at `1` identifies the internal
hom with `ZMod n` as `G`-modules (`TauCeti.InternalHom.zmodEquiv_smul`). Under that identification
`α₀` and `α₂` are scalar multiplication on `H²(G, ZMod n)`, and `α₁` is the cup product of
multiplication in `ZMod n`. -/

-- Preferring the ring path keeps a single additive structure on `ZMod n`, so that the module
-- structure of `H²(G, ZMod n)` below is the one its consumers see.
attribute [local instance 2000] Ring.toAddCommGroup

variable {n : ℕ} {G : Type uG} [Group G] [DistribMulAction G (ZMod n)]
  (htriv : ∀ (g : G) (m : ZMod n), g • m = m)

include htriv

variable [NeZero n] [TopologicalSpace G] [ContinuousSMul G (ZMod n)]

section ContinuousMul

/-! The two statements about `α₂` need only continuous multiplication on `G`. -/

variable [ContinuousMul G]

/-- **`α₂` at trivial `ZMod n` coefficients is scalar multiplication**: `α₂ b φ = φ 1 • b`. -/
theorem dualityMap2_zmod (b : H2 G (ZMod n)) (φ : H0 G (InternalHom G (ZMod n) (ZMod n))) :
    dualityMap2 G (ZMod n) (ZMod n) b φ =
      InternalHom.zmodEquiv G (φ : InternalHom G (ZMod n) (ZMod n)) • b := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [dualityMap2_mk, zmod_smul_mk]
    refine congrArg (fun z : Z2 G (ZMod n) => (z : H2 G (ZMod n)))
      (Subtype.ext (funext fun q => ?_))
    dsimp only
    rw [InternalHom.smul_eq_self_of_smul_eq_self htriv htriv, AddMonoidHom.flip_apply,
      InternalHom.evalPairing_apply, InternalHom.toAddMonoidHom_apply_eq_smul]
    simp [nsmul_eq_mul, mul_comm]

/-- **`α₂` at trivial `ZMod n` coefficients is bijective**, for every group `G` with continuous
multiplication acting trivially on `ZMod n`: under evaluation at `1` it sends `b` to `c ↦ c • b`,
and a homomorphism out of `ZMod n` into a group killed by `n` is determined by its value at `1`. -/
theorem dualityMap2_zmod_bijective : Function.Bijective (dualityMap2 G (ZMod n) (ZMod n)) := by
  -- the identity of `ZMod n` is an invariant element of the internal hom, with value `1` at `1`
  have hid : InternalHom.of G (AddMonoidHom.id (ZMod n)) ∈
      H0 G (InternalHom G (ZMod n) (ZMod n)) :=
    (FixedPoints.mem_addSubgroup _ _ _).2 fun g =>
      InternalHom.smul_eq_self_of_smul_eq_self htriv htriv g _
  constructor
  · intro b b' h
    have := congrArg
      (fun f : H0 G (InternalHom G (ZMod n) (ZMod n)) →+ H2 G (ZMod n) => f ⟨_, hid⟩) h
    simpa [dualityMap2_zmod htriv] using this
  · intro f
    refine ⟨f ⟨_, hid⟩, AddMonoidHom.ext fun φ => ?_⟩
    -- an invariant homomorphism `φ` is `φ 1` times the identity
    have hφ : φ = (InternalHom.zmodEquiv G (φ : InternalHom G (ZMod n) (ZMod n))).val •
        (⟨_, hid⟩ : H0 G (InternalHom G (ZMod n) (ZMod n))) := by
      ext x
      rw [InternalHom.toAddMonoidHom_apply_eq_smul]
      simp [nsmul_eq_mul, mul_comm]
    have hf : f φ = (InternalHom.zmodEquiv G (φ : InternalHom G (ZMod n) (ZMod n))).val •
        f ⟨_, hid⟩ := by
      rw [← map_nsmul, ← hφ]
    rw [dualityMap2_zmod htriv, hf, ← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]

end ContinuousMul

variable [IsTopologicalGroup G]

/-- For a trivial action on `ZMod n`, the first cohomology of `InternalHom G (ZMod n) (ZMod n)` is
that of `ZMod n`, along evaluation at `1`. -/
noncomputable def H1InternalHomZModEquiv :
    H1 G (InternalHom G (ZMod n) (ZMod n)) ≃+ H1 G (ZMod n) :=
  explicitCoeff1Equiv G (InternalHom G (ZMod n) (ZMod n)) (InternalHom.zmodEquiv G)
    continuous_of_discreteTopology continuous_of_discreteTopology (InternalHom.zmodEquiv_smul htriv)

/-- For a trivial action on `ZMod n`, the second cohomology of `InternalHom G (ZMod n) (ZMod n)` is
that of `ZMod n`, along evaluation at `1`. -/
noncomputable def H2InternalHomZModEquiv :
    H2 G (InternalHom G (ZMod n) (ZMod n)) ≃+ H2 G (ZMod n) :=
  explicitMap2Equiv G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMulEquiv.refl G)
    (InternalHom.zmodEquiv G) continuous_of_discreteTopology continuous_of_discreteTopology
    (InternalHom.zmodEquiv_smul htriv)

/-- On cocycle classes, `H1InternalHomZModEquiv` evaluates the cocycle at `1` pointwise: it is the
cocycle pushforward along `TauCeti.InternalHom.zmodEquiv`, whose values are given by
`cocyclesMap1_apply`. -/
theorem H1InternalHomZModEquiv_mk (c : Z1 G (InternalHom G (ZMod n) (ZMod n))) :
    H1InternalHomZModEquiv htriv (c : H1 G (InternalHom G (ZMod n) (ZMod n))) =
      (cocyclesMap1 G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMonoidHom.id G)
        (InternalHom.zmodEquiv G (n := n) (A := ZMod n)).toAddMonoidHom
        continuous_of_discreteTopology (fun g φ => InternalHom.zmodEquiv_smul htriv g φ) c :
          H1 G (ZMod n)) := by
  rw [H1InternalHomZModEquiv, explicitCoeff1Equiv_mk]
  rfl

/-- On cocycle classes, `H2InternalHomZModEquiv` evaluates the cocycle at `1` pointwise: it is the
cocycle pushforward along `TauCeti.InternalHom.zmodEquiv`, whose values are given by
`cocyclesMap2_apply`. -/
theorem H2InternalHomZModEquiv_mk (c : Z2 G (InternalHom G (ZMod n) (ZMod n))) :
    H2InternalHomZModEquiv htriv (c : H2 G (InternalHom G (ZMod n) (ZMod n))) =
      (cocyclesMap2 G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMonoidHom.id G)
        (InternalHom.zmodEquiv G (n := n) (A := ZMod n)).toAddMonoidHom
        continuous_of_discreteTopology (fun g φ => InternalHom.zmodEquiv_smul htriv g φ) c :
          H2 G (ZMod n)) := by
  rw [H2InternalHomZModEquiv]
  -- `explicitMap2Equiv` is sealed, so its `_apply` lemma is used as a term rather than rewritten
  refine ((explicitMap2Equiv_apply G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n)
    (ContinuousMulEquiv.refl G) (InternalHom.zmodEquiv G) continuous_of_discreteTopology
    continuous_of_discreteTopology (InternalHom.zmodEquiv_smul htriv) c).trans
    (explicitMap2_mk G (InternalHom G (ZMod n) (ZMod n)) G (ZMod n) (ContinuousMulEquiv.refl G)
      (InternalHom.zmodEquiv G (n := n) (A := ZMod n)).toAddMonoidHom
      continuous_of_discreteTopology (fun g φ => InternalHom.zmodEquiv_smul htriv g φ) c)).trans ?_
  rfl

/-- **`α₀` at trivial `ZMod n` coefficients is scalar multiplication**: `α₀ m b = m • b`, reading
`b` in `H²(G, ZMod n)` through evaluation at `1`. -/
theorem dualityMap0_zmod (m : H0 G (ZMod n)) (b : H2 G (InternalHom G (ZMod n) (ZMod n))) :
    dualityMap0 G (ZMod n) (ZMod n) m b = (m : ZMod n) • H2InternalHomZModEquiv htriv b := by
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [dualityMap0_mk, H2InternalHomZModEquiv_mk, zmod_smul_mk]
    refine congrArg (fun z : Z2 G (ZMod n) => (z : H2 G (ZMod n)))
      (Subtype.ext (funext fun q => ?_))
    obtain ⟨g, h⟩ := q
    dsimp only
    rw [AddMonoidHom.flip_apply, InternalHom.evalPairing_apply,
      InternalHom.toAddMonoidHom_apply_eq_smul]
    simp [nsmul_eq_mul]

/-- **`α₁` at trivial `ZMod n` coefficients is the cup product of multiplication**:
`α₁ a b = a ⌣ b`, reading `b` in `H¹(G, ZMod n)` through evaluation at `1`. -/
theorem dualityMap1_zmod (a : H1 G (ZMod n)) (b : H1 G (InternalHom G (ZMod n) (ZMod n))) :
    dualityMap1 G (ZMod n) (ZMod n) a b =
      explicitCup11 G (ZMod n) (ZMod n) (ZMod n) AddMonoidHom.mul continuous_mul
        (smul_mul_smul_of_smul_eq_self htriv) a (H1InternalHomZModEquiv htriv b) := by
  induction a using QuotientAddGroup.induction_on with
  | _ x =>
    induction b using QuotientAddGroup.induction_on with
    | _ y =>
      rw [dualityMap1_mk, H1InternalHomZModEquiv_mk]
      -- `explicitCup11_mk` is applied as a term: the continuity of multiplication is stated at
      -- `fun p => p.1 * p.2`, which `rw` does not identify with the pairing `AddMonoidHom.mul`
      refine Eq.trans ?_ (explicitCup11_mk G (ZMod n) (ZMod n) (ZMod n) AddMonoidHom.mul
        continuous_mul (smul_mul_smul_of_smul_eq_self htriv) x _).symm
      refine congrArg (fun z : Z2 G (ZMod n) => (z : H2 G (ZMod n)))
        (Subtype.ext (funext fun q => ?_))
      obtain ⟨g, h⟩ := q
      dsimp only
      rw [InternalHom.smul_eq_self_of_smul_eq_self htriv htriv, AddMonoidHom.flip_apply,
        InternalHom.evalPairing_apply, InternalHom.toAddMonoidHom_apply_eq_smul]
      simp [htriv]

/-- **`α₀` at trivial `𝔽_p` coefficients is bijective when `H²(G, 𝔽_p)` is one-dimensional**:
under evaluation at `1` it sends `c` to multiplication by `c`, and every endomorphism of a
one-dimensional space is a scalar. -/
theorem dualityMap0_zmod_bijective_of_finrank_eq_one [Fact n.Prime]
    (hrank : Module.finrank (ZMod n) (H2 G (ZMod n)) = 1) :
    Function.Bijective (dualityMap0 G (ZMod n) (ZMod n)) := by
  have : Nontrivial (H2 G (ZMod n)) :=
    Module.nontrivial_of_finrank_pos (R := ZMod n) (hrank ▸ Nat.one_pos)
  constructor
  · intro m m' h
    obtain ⟨w, hw⟩ := exists_ne (0 : H2 G (ZMod n))
    have := congrArg (fun f : H2 G (InternalHom G (ZMod n) (ZMod n)) →+ H2 G (ZMod n) =>
      f ((H2InternalHomZModEquiv htriv).symm w)) h
    simp only [dualityMap0_zmod htriv, AddEquiv.apply_symm_apply] at this
    exact Subtype.ext (smul_left_injective (ZMod n) hw this)
  · intro f
    obtain ⟨c, hc⟩ := ((f.comp (H2InternalHomZModEquiv htriv).symm.toAddMonoidHom).toZModLinearMap
      n).existsUnique_eq_smul_id_of_finrank_eq_one hrank |>.exists
    refine ⟨⟨c, (FixedPoints.mem_addSubgroup _ _ _).2 fun g => htriv g c⟩,
      AddMonoidHom.ext fun b => ?_⟩
    rw [dualityMap0_zmod htriv]
    have := LinearMap.congr_fun hc (H2InternalHomZModEquiv htriv b)
    simpa using this.symm

end TrivialZMod

end TauCeti.ContCohomology
