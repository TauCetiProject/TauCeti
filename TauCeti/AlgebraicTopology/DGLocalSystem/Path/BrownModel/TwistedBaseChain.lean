/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.Path.BrownModel.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.LocalCoefficients.Pushforward
import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

/-!
# Twisted base chains of a Brown model

Let `L` be a classical local system on a pointed space `(X, b)`, with fibre `L_b` at `b`. The chains
`C_*(P_b X; R)` on the Moore paths starting at `b` push forward to the cubical chains of `X` with
coefficients in `L` along the end point map `P_b X → X`: the based path space is contractible, so a
coefficient `a ∈ L_b` transports along the end point of any path in `P_b X` from the constant path
to the origin of a cube. This is the **twisted end point push-forward**
(`TauCeti.twistedEndpointPushforward`), in each dimension `n` a bilinear map

`C_*(P_b X; R) × L_b → C_n(X; L)`.

It commutes with the boundaries (`TauCeti.boundary_twistedEndpointPushforward`), and it is
balanced over the loop chains: a chain `α` on the Moore loops at `b`, acting on the paths by
concatenation in front, can be moved to the coefficient, where it acts through its degree-zero part
by the monodromy of `L` (`TauCeti.twistedEndpointPushforward_smul`),

`ev_*(α · c, a) = ev_*(c, a · α)`.

Indeed a loop `ω` concatenated in front of a path does not move its end point, and the coefficient
is then transported along `ω` first. A chain of positive dimension on the loops pushes forward to
degenerate cubes, which vanish in the normalized chains.

For a Brown model `M` at `b` (`TauCeti.BrownModel`), with twisting cocycle `m` and comparison
`g : K_m → C_*(P_b X; R)`, the **twisted base chain** of a generator `x` with coefficient `a`
(`TauCeti.BrownModel.twistedBaseChain`) is `e_x^a = ev_*(g(x), a)`. It vanishes outside the
dimension of `x` (`TauCeti.BrownModel.twistedBaseChain_eq_zero`), and the equation
`g(m_x) = ∂ g(x)` of the model gives
(`TauCeti.BrownModel.boundary_twistedBaseChain`)

`∂ e_x^a = ∑_y e_y^{a · m_{x,y}}`,

where `m_{x,y}` acts on `L_b` through its degree-zero part in the group ring of `π₁(X, b)`. So
`x ⊗ a ↦ e_x^a` is a chain map from the twisted complex of the classical DG local system of `L`
(`TauCeti.classicalDGLocalSystem`), on the coefficient vectors `P →₀ L_b`, to the cubical chains of
`X` with coefficients in `L` (`TauCeti.BrownModel.boundary_twistedBaseChainMap`). It is the
counterpart with local coefficients of the base chain `x ↦ e_x` of `TauCeti.BrownModel.baseChain`,
whose boundary coefficients are the augmentations `ε(m_{x,y})`.

This chain map is the comparison between the twisted complex of a Brown model with classical
coefficients and the chains of `X` with local coefficients. This file does not show that it is a
quasi-isomorphism.

## Main definitions

* `TauCeti.twistedEndpointPushforward L H n`: the twisted end point push-forward
  `C_*(P_b X; R) → Hom(L_b, C_n(X; L))`.
* `TauCeti.BrownModel.twistedBaseChain M L n x`: the twisted base chain `a ↦ e_x^a` of a generator.
* `TauCeti.BrownModel.twistedBaseChainMap M L n`: its extension `P →₀ L_b → C_n(X; L)`.

## Main results

* `TauCeti.boundary_twistedEndpointPushforward`: the push-forward commutes with the boundaries.
* `TauCeti.twistedEndpointPushforward_smul`: it is balanced over the loop chains.
* `TauCeti.BrownModel.boundary_twistedBaseChain`: `∂ e_x^a = ∑_y e_y^{a · m_{x,y}}`.
* `TauCeti.BrownModel.boundary_twistedBaseChainMap`: the twisted base chains form a chain map from
  the twisted complex of the classical DG local system.

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4 and §7.1.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

universe u w uH uP

namespace TauCeti

open LocalCoefficientSystem LocalCoefficientSystem.NormalizedTwistedCubicalChain

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {b : X}
  (L : LocalCoefficientSystem.{u, u, w} R X) (H : Type uH)

section Endpoint

/-- The **twisted end point push-forward** in dimension `n`: a chain of dimension `n` on the Moore
paths from `b` with a coefficient `a ∈ L_b` goes to its push-forward along the end point map, with
`a` transported along the end points of paths from the constant path to the origins of its cubes.
The chains of other dimensions go to `0`. -/
def twistedEndpointPushforward (n : ℕ) :
    cubicalChainModule (MoorePathFrom X b) H R →ₗ[R]
      L.obj (FundamentalGroupoid.mk b) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  ((scalarPushforward L (MoorePathFrom.endpoint X b) (MoorePathFrom.refl X b) n).compl₂
      (L.map (eqToHom (congrArg FundamentalGroupoid.mk MoorePathFrom.endpoint_refl.symm))).hom) ∘ₗ
    DirectSum.component R ℕ (fun n ↦ NormalizedCubicalChain (MoorePathFrom X b) R n) n ∘ₗ
      (cubicalChainModuleEquiv (MoorePathFrom X b) H R).toLinearMap

variable {L H}

/-- On a chain of dimension `n`, the twisted end point push-forward is the twisted push-forward
along the end point map from the constant path at `b`. -/
@[simp]
theorem twistedEndpointPushforward_lof {n : ℕ} (c : NormalizedCubicalChain (MoorePathFrom X b) R n)
    (a : L.obj (FundamentalGroupoid.mk b)) :
    twistedEndpointPushforward L H n (cubicalChainModuleLof (MoorePathFrom X b) H R n c) a =
      scalarPushforward L (MoorePathFrom.endpoint X b) (MoorePathFrom.refl X b) n c
        (L.map (eqToHom (congrArg FundamentalGroupoid.mk MoorePathFrom.endpoint_refl.symm)) a) := by
  simp [twistedEndpointPushforward]

/-- The twisted end point push-forward in dimension `n` vanishes on the chains of every other
dimension. -/
theorem twistedEndpointPushforward_lof_of_ne {m n : ℕ} (h : m ≠ n)
    (c : NormalizedCubicalChain (MoorePathFrom X b) R m) :
    twistedEndpointPushforward L H n (cubicalChainModuleLof (MoorePathFrom X b) H R m c) = 0 := by
  ext a
  simp [twistedEndpointPushforward, DirectSum.component.of, h]

/-- **The twisted end point push-forward commutes with the boundaries.** -/
theorem boundary_twistedEndpointPushforward (n : ℕ)
    (x : cubicalChainModule (MoorePathFrom X b) H R) (a : L.obj (FundamentalGroupoid.mk b)) :
    boundary L n (twistedEndpointPushforward L H (n + 1) x a) =
      twistedEndpointPushforward L H n
        (cubicalChainModuleDifferential (MoorePathFrom X b) H R x) a := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | lof m c =>
    rcases m with _ | m
    · rw [twistedEndpointPushforward_lof_of_ne (by omega), cubicalChainModuleDifferential_lof_zero]
      simp
    · rw [cubicalChainModuleDifferential_lof_succ]
      by_cases hm : m = n
      · subst hm
        rw [twistedEndpointPushforward_lof, twistedEndpointPushforward_lof,
          boundary_scalarPushforward]
      · rw [twistedEndpointPushforward_lof_of_ne (by omega),
          twistedEndpointPushforward_lof_of_ne hm]
        simp

/-- A cube of positive dimension on the Moore loops at `b`, acting on a cube of paths by
concatenation in front, gives a cube whose end point does not depend on the first coordinate. -/
private theorem isDegenerate_endpoint_comp_leftActMap {p q : ℕ}
    (a : SingularCube (MooreLoopSpace X b) (p + 1)) (d : SingularCube (MoorePathFrom X b) q) :
    SingularCube.IsDegenerate ((MoorePathFrom.endpoint X b).comp
      ((leftActMap (MooreLoopSpace X b) (MoorePathFrom X b)).comp
        (SingularCube.crossProduct a d))) := by
  have h : (MoorePathFrom.endpoint X b).comp
      ((leftActMap (MooreLoopSpace X b) (MoorePathFrom X b)).comp
        (SingularCube.crossProduct a d)) =
      (MoorePathFrom.endpoint X b).comp
        ((leftActMap (MooreLoopSpace X b) (MoorePathFrom X b)).comp
          (SingularCube.crossProduct ((ContinuousMap.const _ 1).comp a)
            ((ContinuousMap.id _).comp d))) := by
    rw [SingularCube.crossProduct_comp]
    ext x
    simp [leftActMap_apply]
  rw [h]
  -- The constant cube at the unit does not depend on its first coordinate.
  have hconst : SingularCube.IsDegenerate
      ((ContinuousMap.const (MooreLoopSpace X b) (1 : MooreLoopSpace X b)).comp a) :=
    SingularCube.isDegenerate_iff.2 ⟨0, SingularCube.isDegenerateAt_iff.2 fun x t ↦ by simp⟩
  exact (((SingularCube.isDegenerate_crossProduct_iff _ _).2 (Or.inl hconst)).comp _).comp _

/-- A chain of positive dimension on the Moore loops at `b`, acting on a chain of paths, pushes
forward to `0`. -/
private theorem scalarPushforward_leftAct_succ {p q : ℕ}
    (z : NormalizedCubicalChain (MooreLoopSpace X b) R (p + 1))
    (c : NormalizedCubicalChain (MoorePathFrom X b) R q)
    (a : L.obj (FundamentalGroupoid.mk (MoorePathFrom.endpoint X b (MoorePathFrom.refl X b)))) :
    scalarPushforward L (MoorePathFrom.endpoint X b) (MoorePathFrom.refl X b) (p + 1 + q)
      (NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathFrom X b) R (p + 1) q z c)
        a = 0 := by
  induction z using NormalizedCubicalChain.induction_on with
  | zero => simp
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz', add_zero]
  | smul r z hz => simp only [map_smul, LinearMap.smul_apply, hz, smul_zero]
  | ofCube e =>
    induction c using NormalizedCubicalChain.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [map_add, LinearMap.add_apply, hc, hc', add_zero]
    | smul r c hc => simp only [map_smul, LinearMap.smul_apply, hc, smul_zero]
    | ofCube d =>
      rw [NormalizedCubicalChain.leftAct_ofCube, scalarPushforward_ofCube]
      exact ofCube_eq_zero (isDegenerate_endpoint_comp_leftActMap e d) _

/-- Concatenation in front with the Moore loop `ω`, as a self-map of the based path space. -/
private def leftActBy (ω : MooreLoopSpace X b) : C(MoorePathFrom X b, MoorePathFrom X b) :=
  ⟨(ω • ·), continuous_const_smul ω⟩

private theorem leftActBy_apply (ω : MooreLoopSpace X b) (y : MoorePathFrom X b) :
    leftActBy ω y = ω • y :=
  (rfl)

/-- Concatenation in front with a Moore loop does not move the end point. -/
private theorem endpoint_comp_leftActBy (ω : MooreLoopSpace X b) :
    (MoorePathFrom.endpoint X b).comp (leftActBy ω) = MoorePathFrom.endpoint X b :=
  ContinuousMap.ext fun y ↦ by simp [leftActBy_apply]

/-- The point chain of a Moore loop `ω` acts on a chain of paths as the push-forward along the
concatenation with `ω` in front. -/
private theorem cubicalChainModuleLof_leftAct_point (ω : MooreLoopSpace X b) {q : ℕ}
    (c : NormalizedCubicalChain (MoorePathFrom X b) R q) :
    cubicalChainModuleLof (MoorePathFrom X b) H R (0 + q)
        (NormalizedCubicalChain.leftAct (MooreLoopSpace X b) (MoorePathFrom X b) R 0 q
          (NormalizedCubicalChain.ofCube _ R (SingularCube.point ω)) c) =
      cubicalChainModuleLof (MoorePathFrom X b) H R q
        (NormalizedCubicalChain.map R (leftActBy ω) q c) := by
  have h : (leftActMap (MooreLoopSpace X b) (MoorePathFrom X b)).comp
      ((ContinuousMap.const _ ω).prodMk (ContinuousMap.id _)) = leftActBy ω :=
    ContinuousMap.ext fun y ↦ by simp [leftActMap_apply, leftActBy_apply]
  rw [← cubicalChainModuleLof_cast (Nat.zero_add q), NormalizedCubicalChain.leftAct_def,
    ← NormalizedCubicalChain.map_cast, NormalizedCubicalChain.crossProduct_point_left, ← h,
    NormalizedCubicalChain.map_map]

/-- A path in the based path space from the constant path to the loop `ω` read as a path, by
truncation of `ω`. Its end points run along `ω`. -/
private def truncatePath (ω : MooreLoopSpace X b) :
    Path (MoorePathFrom.refl X b) (leftActBy ω (MoorePathFrom.refl X b)) where
  toFun t := MoorePathFrom.truncateHomotopy (t, leftActBy ω (MoorePathFrom.refl X b))
  continuous_toFun := by fun_prop
  source' := MoorePathFrom.truncateHomotopy.apply_zero _
  target' := MoorePathFrom.truncateHomotopy.apply_one _

/-- The end points of the truncations of `ω` run along `ω`. -/
private theorem endpoint_truncatePath (ω : MooreLoopSpace X b) (t : unitInterval) :
    MoorePathFrom.endpoint X b (truncatePath ω t) = ω.toPath t := by
  -- The truncation stops at time `t * length`, while `toPath` reads `ω` at time `length * t`.
  rw [MooreLoopSpace.toPath_apply, mul_comm]
  simp [truncatePath, leftActBy_apply, MoorePathFrom.smul_eq_leftAct,
    MoorePathFrom.endpoint_apply, MoorePathFrom.toMoorePath_truncateHomotopy]

/-- **The monodromy of concatenation with a loop.** The end points of the truncations of `ω`,
read between the fibres at `b`, are the loop `ω` itself. -/
private theorem eqToHom_comp_mk_truncatePath_comp_eqToHom (ω : MooreLoopSpace X b)
    (hb : MoorePathFrom.endpoint X b (MoorePathFrom.refl X b) = b)
    (hω : MoorePathFrom.endpoint X b (leftActBy ω (MoorePathFrom.refl X b)) = b) :
    eqToHom (congrArg FundamentalGroupoid.mk hb.symm) ≫
        Path.Homotopic.Quotient.mk ((truncatePath ω).map (MoorePathFrom.endpoint X b).continuous) ≫
          eqToHom (congrArg FundamentalGroupoid.mk hω) =
      Path.Homotopic.Quotient.mk ω.toPath := by
  rw [FundamentalGroupoid.conj_eqToHom hb.symm hω.symm, ← Path.Homotopic.Quotient.mk_cast]
  congr 1
  ext t
  simp [endpoint_truncatePath]

/-- Transporting a coefficient at `b` to the end point of the constant path, and then along the end
points of paths to the loop `ω` read as a path, is transporting it along `ω` first. -/
private theorem eqToHom_comp_pathClass_comp_eqToHom (ω : MooreLoopSpace X b)
    (h : FundamentalGroupoid.mk
        (((MoorePathFrom.endpoint X b).comp (leftActBy ω)) (MoorePathFrom.refl X b)) =
      FundamentalGroupoid.mk (MoorePathFrom.endpoint X b (MoorePathFrom.refl X b))) :
    eqToHom (congrArg FundamentalGroupoid.mk MoorePathFrom.endpoint_refl.symm) ≫
        (MoorePathFrom.endpoint X b).pathClass (MoorePathFrom.refl X b)
          (leftActBy ω (MoorePathFrom.refl X b)) ≫ eqToHom h =
      Path.Homotopic.Quotient.mk ω.toPath ≫
        eqToHom (congrArg FundamentalGroupoid.mk MoorePathFrom.endpoint_refl.symm) := by
  have hω : MoorePathFrom.endpoint X b (leftActBy ω (MoorePathFrom.refl X b)) = b := by
    rw [leftActBy_apply, MoorePathFrom.smul_eq_leftAct, MoorePathFrom.endpoint_leftAct,
      MoorePathFrom.endpoint_refl]
  rw [ContinuousMap.pathClass_eq_mk _ (truncatePath ω),
    ← eqToHom_comp_mk_truncatePath_comp_eqToHom ω MoorePathFrom.endpoint_refl hω]
  simp

/-- **The twisted end point push-forward is balanced over the loop chains**: a chain `α` on the
Moore loops at `b`, concatenated in front of the paths, can be moved to the coefficient, on which it
acts by the monodromy of its degree-zero part. -/
theorem twistedEndpointPushforward_smul (n : ℕ) (α : loopChainAlgebra X b R)
    (x : cubicalChainModule (MoorePathFrom X b) H R) (a : L.obj (FundamentalGroupoid.mk b)) :
    twistedEndpointPushforward L H n (α • x) a = twistedEndpointPushforward L H n x (op α • a) := by
  induction x using cubicalChainModule.induction_on with
  | add x x' hx hx' => simp only [smul_add, map_add, LinearMap.add_apply, hx, hx']
  | lof q c =>
    induction α using DirectSum.induction_on with
    | zero => simp
    | add α α' hα hα' =>
      simp only [add_smul, map_add, LinearMap.add_apply, hα, hα', MulOpposite.op_add]
    | of p z =>
      rw [← DirectSum.lof_eq_of R, lof_smul_cubicalChainModuleLof]
      rcases p with _ | p
      · induction z using NormalizedCubicalChain.induction_on with
        | zero => simp
        | add z z' hz hz' =>
          simp only [map_add, LinearMap.add_apply, MulOpposite.op_add, add_smul, hz, hz']
        | smul r z hz =>
          simp only [map_smul, LinearMap.smul_apply, op_smul, smul_assoc, hz]
        | ofCube e =>
          rw [SingularCube.eq_point e, cubicalChainModuleLof_leftAct_point,
            op_smul_eq_classicalAction, classicalAction_lof_point]
          simp only [LinearEquiv.coe_coe, transport_apply]
          by_cases hq : q = n
          · subst hq
            rw [twistedEndpointPushforward_lof, twistedEndpointPushforward_lof,
              scalarPushforward_map (leftActBy _) (MoorePathFrom.refl X b),
              scalarPushforward_congr (endpoint_comp_leftActBy _)]
            congr 1
            simp only [← ModuleCat.comp_apply, ← Functor.map_comp, Category.assoc,
              eqToHom_comp_pathClass_comp_eqToHom]
          · rw [twistedEndpointPushforward_lof_of_ne hq, twistedEndpointPushforward_lof_of_ne hq]
            simp
      · rw [op_smul_eq_classicalAction, classicalAction_lof_succ, LinearMap.zero_apply,
          map_zero]
        by_cases hq : p + 1 + q = n
        · subst hq
          rw [twistedEndpointPushforward_lof, scalarPushforward_leftAct_succ]
        · rw [twistedEndpointPushforward_lof_of_ne hq]
          simp

end Endpoint

namespace BrownModel

variable {L H} {P : Type uP} {ind : P → ℤ} (M : BrownModel X b H R P ind)

/-- The **twisted base chain** `a ↦ e_x^a` of a generator `x` of a Brown model, in dimension `n`:
the twisted end point push-forward of the image of `x` in the chains on the based path space, with
coefficient `a ∈ L_b`. It vanishes unless `n` is the index of `x`. -/
def twistedBaseChain (L : LocalCoefficientSystem.{u, u, w} R X) (n : ℕ) (x : P) :
    L.obj (FundamentalGroupoid.mk b) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  twistedEndpointPushforward L H n (M.comparison x)

theorem twistedBaseChain_def (n : ℕ) (x : P) :
    M.twistedBaseChain L n x = twistedEndpointPushforward L H n (M.comparison x) :=
  (rfl)

/-- The twisted base chain of a generator vanishes outside the dimension of the generator. -/
theorem twistedBaseChain_eq_zero {n : ℕ} {x : P} (hn : (n : ℤ) ≠ ind x) :
    M.twistedBaseChain L n x = 0 := by
  rcases mem_cubicalChainModuleGrading_iff.1 (M.comparison_mem x) with h | ⟨m, c, hm, h⟩
  · rw [twistedBaseChain_def, h, map_zero]
  · rw [twistedBaseChain_def, ← h, twistedEndpointPushforward_lof_of_ne (by omega)]

/-- **The boundary of a twisted base chain**: `∂ e_x^a = ∑_y e_y^{a · m_{x,y}}`, where the row
`m_{x,y}` of the twisting cocycle acts on `L_b` through its degree-zero part, by monodromy. -/
theorem boundary_twistedBaseChain (n : ℕ) (x : P) (a : L.obj (FundamentalGroupoid.mk b)) :
    boundary L n (M.twistedBaseChain L (n + 1) x a) =
      (M.cocycle.m x).sum fun y α ↦ M.twistedBaseChain L n y (op α • a) := by
  rw [twistedBaseChain_def, boundary_twistedEndpointPushforward, ← M.linearCombination_comparison_m]
  simp [Finsupp.linearCombination_apply, map_finsuppSum, twistedEndpointPushforward_smul,
    twistedBaseChain_def]

/-- The **twisted base chain map** in dimension `n`: the coefficient vector `∑_x x ⊗ a_x` goes to
`∑_x e_x^{a_x}`. -/
def twistedBaseChainMap (L : LocalCoefficientSystem.{u, u, w} R X) (n : ℕ) :
    (P →₀ L.obj (FundamentalGroupoid.mk b)) →ₗ[R] L.NormalizedTwistedCubicalChain n :=
  Finsupp.lsum R (M.twistedBaseChain L n)

/-- The twisted base chain map on an elementary vector is the twisted base chain. -/
@[simp]
theorem twistedBaseChainMap_single (n : ℕ) (x : P) (a : L.obj (FundamentalGroupoid.mk b)) :
    M.twistedBaseChainMap L n (Finsupp.single x a) = M.twistedBaseChain L n x a := by
  simp [twistedBaseChainMap]

/-- **The twisted base chains form a chain map** from the twisted complex of the classical DG local
system of `L`, on the coefficient vectors `P →₀ L_b`, to the normalized cubical chains of `X` with
coefficients in `L`. -/
theorem boundary_twistedBaseChainMap (n : ℕ) (f : P →₀ L.obj (FundamentalGroupoid.mk b)) :
    boundary L n (M.twistedBaseChainMap L (n + 1) f) =
      M.twistedBaseChainMap L n
        (M.cocycle.coefficientDifferential (isDGRightModule_fiber L) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [map_add, hf, hf']
  | single x a =>
    rw [M.cocycle.coefficientDifferential_single (isDGRightModule_fiber L) x
        ((mem_trivialGrading_iff R _).2 (Or.inl rfl)), twistedBaseChainMap_single,
      boundary_twistedBaseChain]
    simp [map_finsuppSum]

end BrownModel

end TauCeti
