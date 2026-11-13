/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Subpath
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.Topology.PathSpace.Prepend

/-!
# Conjugating loops by a path, and base-point change of `π₂`

A path `p` from `x` to `y` conjugates loops at `x` into loops at `y`:
`Path.conjLoop p ℓ = p⁻¹ ⬝ ℓ ⬝ p`. This is a continuous map `Ω X x → Ω X y`, but it is not
based: it sends the constant loop at `x` to the loop `p⁻¹ ⬝ p` (with a constant middle piece),
which is only contractible. `Path.conjLoopContraction p` is a canonical contraction, the path
of loops `a ↦ q_a⁻¹ ⬝ q_a` along the tails `q_a` of `p` from time `a`. The map on fundamental
groups of loop spaces induced by `Path.conjLoop p`, followed by base-point change along this
contraction, is the **conjugation transport**
`Path.loopSpaceTransport p : π₁(Ω X x, refl x) →* π₁(Ω X y, refl y)`.

Through the identification `π₁(Ω X x, refl x) ≃* π₂(X, x)`
(`HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv`), conjugation transport is base-point change
of `π₂` along `p`, the transport `TauCeti.homotopyGroupTransport p` of
`TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange`
(`HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport`). The proof deforms the
path: the initial segments `p_r` of `p`, from `x` to `p r`, give squares
`(s, t) ↦ (c_r⁻¹ ⬝ conj_{p_r}(α) ⬝ c_r)(s)(t)` whose boundary is the point `p r`, so they form a
homotopy of generalized loops along `p` in the sense of `TauCeti.GenLoop.HomotopyAlong`. At
`r = 0` the segment is constant, and conjugating by a constant path acts trivially
(`Path.loopSpaceTransport_refl`), because it only reparametrizes loops.

In the loop-space model of `π₂`, a sphere at `x` is a loop of loops at the constant loop, and
gluing it at the centre of a disc bounding a loop `γ` is postcomposition in the fundamental
groupoid of `Ω X x`. Conjugating discs by `p` therefore moves discs bounding `γ` to discs
bounding `p⁻¹ ⬝ γ ⬝ p`, and the result here says that the spheres glued to them move by
base-point change of `π₂`. In particular they keep their Hurewicz classes
(`HomotopyGroup.hurewicz_homotopyGroupTransport`).

## Main definitions

* `Path.conjLoop p : C(Ω X x, Ω X y)`: conjugation of loops by `p`.
* `Path.conjLoopContraction p`: the contraction of `p⁻¹ ⬝ refl ⬝ p` to the constant loop at `y`.
* `Path.loopSpaceTransport p`: the conjugation transport on fundamental groups of loop spaces.

## Main results

* `Path.map_comp_conjLoopContraction`: conjugation intertwines the action of loops of loops
  with conjugation transport, in the fundamental groupoid of `Ω X y`.
* `Path.loopSpaceTransport_refl`: conjugation by a constant path acts trivially.
* `HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport`: conjugation transport is
  base-point change of `π₂` along `p`.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.1, on the action of paths on higher homotopy groups
  and the loop-space description `π_(n + 1)(X) ≅ π_n(Ω X)`.
-/

public section

noncomputable section

open CategoryTheory unitInterval
open scoped Topology Topology.Homotopy

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- **Conjugation of loops by a path** `p` from `x` to `y`: the loop `p⁻¹ ⬝ (ℓ ⬝ p)` at `y`. -/
def conjLoop (p : Path x y) : C(Ω X x, Ω X y) where
  toFun ℓ := p.symm.trans (ℓ.trans p)
  continuous_toFun := continuous_trans.comp
    (continuous_const.prodMk (continuous_trans.comp (continuous_id.prodMk continuous_const)))

@[simp]
theorem conjLoop_apply (p : Path x y) (ℓ : Ω X x) : p.conjLoop ℓ = p.symm.trans (ℓ.trans p) :=
  (rfl)

/-- The tail `p.subpath a 1` of `p` from time `a`, as a path ending at `y`. -/
private def tail (p : Path x y) (a : I) : Path (p a) y :=
  (p.subpath a 1).cast rfl p.target.symm

private theorem tail_apply (p : Path x y) (a u : I) : p.tail a u = p.subpath a 1 u :=
  (rfl)

/-- **The contraction of the conjugated constant loop**: the path of loops at `y` whose value at
`a` is `q_a⁻¹ ⬝ (refl ⬝ q_a)` for the tail `q_a` of `p` from time `a`. It starts at
`p.conjLoop (Path.refl x)` and ends at the constant loop. -/
def conjLoopContraction (p : Path x y) : Path (p.conjLoop (refl x)) (refl y) where
  toFun a := (p.tail a).symm.trans ((refl (p a)).trans (p.tail a))
  continuous_toFun := by
    have ht : Continuous ↿p.tail := p.subpath_continuous_family.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    exact continuous_uncurry_iff.1 <| trans_continuous_family _
      (symm_continuous_family _ ht) _
      (trans_continuous_family _ (p.continuous.comp continuous_fst) _ ht)
  source' := by
    ext t
    simp [tail, trans_apply]
  target' := by
    ext t
    simp [tail_apply, trans_apply]

theorem conjLoopContraction_apply (p : Path x y) (a : I) :
    p.conjLoopContraction a =
      ((p.subpath a 1).cast rfl p.target.symm).symm.trans
        ((refl (p a)).trans ((p.subpath a 1).cast rfl p.target.symm)) :=
  (rfl)

/-- **Conjugation transport** on fundamental groups of loop spaces along a path `p` from `x` to
`y`: the map induced by conjugation of loops by `p`, followed by base-point change along the
contraction `Path.conjLoopContraction p`. It is base-point change of `π₂` along `p`
(`HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport`). -/
def loopSpaceTransport (p : Path x y) :
    FundamentalGroup (Ω X x) (refl x) →* FundamentalGroup (Ω X y) (refl y) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath p.conjLoopContraction).toMonoidHom.comp
    (FundamentalGroup.map p.conjLoop (refl x))

theorem loopSpaceTransport_apply (p : Path x y) (a : FundamentalGroup (Ω X x) (refl x)) :
    p.loopSpaceTransport a =
      .of ((Homotopic.Quotient.mk p.conjLoopContraction).symm.trans
        (((FundamentalGroupoid.map p.conjLoop).map a.asHom).trans
          (Homotopic.Quotient.mk p.conjLoopContraction))) := by
  rw [loopSpaceTransport, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    FundamentalGroup.fundamentalGroupMulEquivOfPath_apply]
  -- `FundamentalGroup.map` acts on the underlying arrow by `FundamentalGroupoid.map`
  rfl

/-- **Conjugation intertwines loops of loops with conjugation transport**: in the fundamental
groupoid of `Ω X y`, the image under `Path.conjLoop p` of a loop of loops at the constant loop,
followed by the contraction `Path.conjLoopContraction p`, is the contraction followed by the
conjugation transport of the loop of loops. -/
theorem map_comp_conjLoopContraction (p : Path x y)
    (a : FundamentalGroup (Ω X x) (refl x)) :
    (FundamentalGroupoid.map p.conjLoop).map a.asHom ≫
        Homotopic.Quotient.mk p.conjLoopContraction =
      Homotopic.Quotient.mk p.conjLoopContraction ≫ (p.loopSpaceTransport a).asHom := by
  rw [loopSpaceTransport_apply]
  -- the inverse in the fundamental groupoid is the reversed path class
  have h := congrArg (· ≫ (FundamentalGroupoid.map p.conjLoop).map a.asHom ≫
    Homotopic.Quotient.mk p.conjLoopContraction)
      (Groupoid.comp_inv (Homotopic.Quotient.mk p.conjLoopContraction))
  rw [Category.id_comp] at h
  exact h.symm.trans (Category.assoc _ _ _)

/-! ### Conjugation by a constant path -/

/-- The reparametrization of `I` by which conjugation with a constant path rescales a loop. -/
private def conjReparam : Path (0 : I) 1 :=
  (refl 0).symm.trans ((⟨ContinuousMap.id I, rfl, rfl⟩ : Path (0 : I) 1).trans (refl 1))

private theorem conjLoop_refl (ℓ : Ω X x) :
    (refl x).conjLoop ℓ =
      ℓ.reparam conjReparam conjReparam.continuous conjReparam.source conjReparam.target := by
  ext t
  rw [coe_reparam, Function.comp_apply, conjLoop_apply, conjReparam]
  simp only [trans_apply, refl_symm, refl_apply]
  split_ifs
  exacts [ℓ.source.symm, rfl, ℓ.target.symm]

/-- The homotopy from the identity of `Ω X x` to conjugation by the constant path, which
reparametrizes every loop in the same way (`Path.reparamHomotopy`). It fixes the constant
loop. -/
private def conjLoopReflHomotopy (x : X) :
    (ContinuousMap.id (Ω X x)).Homotopy (refl x).conjLoop :=
  (reparamHomotopy conjReparam conjReparam.continuous conjReparam.source
    conjReparam.target).cast rfl (ContinuousMap.ext fun ℓ => (conjLoop_refl ℓ).symm)

private theorem conjLoopContraction_refl_apply (a : I) :
    (refl x).conjLoopContraction a = refl x := by
  ext t
  simp [conjLoopContraction_apply, trans_apply, subpath]

private theorem evalAt_conjLoopReflHomotopy (x : X) :
    (conjLoopReflHomotopy x).evalAt (refl x) = (refl x).conjLoopContraction.symm := by
  -- every point of both paths is the constant loop
  refine Path.ext (funext fun u => ?_)
  have h : (conjLoopReflHomotopy x).evalAt (refl x) u = refl x := by
    rw [ContinuousMap.Homotopy.evalAt_apply]
    ext t
    -- `Path.Homotopy.reparam` evaluates the constant loop, so it is constant by definition
    exact (congrArg (fun ℓ : Ω X x => ℓ t) (reparamHomotopy_apply _ _ _ _ u _)).trans rfl
  exact h.trans (conjLoopContraction_refl_apply (σ u)).symm

/-- The double loop `c⁻¹ ⬝ (conj_p α ⬝ c)` representing the conjugation transport of the class
of `α`, where `c` is the contraction `Path.conjLoopContraction p`. -/
private def conjDoubleLoop (p : Path x y) (α : Ω (Ω X x) (refl x)) :
    Ω (Ω X y) (refl y) :=
  p.conjLoopContraction.symm.trans ((α.map p.conjLoop.continuous).trans p.conjLoopContraction)

private theorem loopSpaceTransport_fromPath_mk (p : Path x y) (α : Ω (Ω X x) (refl x)) :
    p.loopSpaceTransport (FundamentalGroup.fromPath (.mk α)) =
      FundamentalGroup.fromPath (.mk (p.conjDoubleLoop α)) := by
  simp [loopSpaceTransport, conjDoubleLoop, FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    Homotopic.Quotient.mk_map]

/-- **Conjugation by a constant path acts trivially** on the fundamental group of the loop
space. -/
@[simp]
theorem loopSpaceTransport_refl (x : X) :
    (refl x).loopSpaceTransport = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => ?_
  have hid : FundamentalGroup.map (ContinuousMap.id (Ω X x)) (refl x) g = g :=
    DFunLike.congr_fun (FundamentalGroup.map_id _) g
  -- freely homotopic maps agree on `π₁` up to base-point change along the trace
  have h : (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (refl x).conjLoopContraction).symm g =
        FundamentalGroup.map (refl x).conjLoop (refl x) g := by
    have h := (conjLoopReflHomotopy x).fundamentalGroupMulEquivOfPath_evalAt_map (refl x) g
    rw [hid, evalAt_conjLoopReflHomotopy] at h
    rwa [← FundamentalGroup.fundamentalGroupMulEquivOfPath_symm]
  rw [loopSpaceTransport, MonoidHom.comp_apply, ← h, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.id_apply]

/-! ### Conjugation along a continuous family of paths -/

/-- The double loops `conjDoubleLoop q α` depend only on the values of `q`. -/
private theorem conjDoubleLoop_congr {b b' : X} (q : Path x b) (q' : Path x b')
    (h : ∀ u, q u = q' u) (α : Ω (Ω X x) (refl x)) (s t : I) :
    q.conjDoubleLoop α s t = q'.conjDoubleLoop α s t := by
  obtain rfl : b = b' := q.target.symm.trans ((h 1).trans q'.target)
  obtain rfl : q = q' := Path.ext (funext h)
  rfl

section Family

variable {ι : Type*} [TopologicalSpace ι] {b : ι → X} (q : ∀ i, Path x (b i))

private theorem continuous_conjLoopContraction_family (hq : Continuous ↿q) :
    Continuous fun w : (ι × I) × I => (q w.1.1).conjLoopContraction w.1.2 w.2 := by
  have ht : Continuous ↿fun v : ι × I => (q v.1).tail v.2 :=
    hq.comp (continuous_fst.fst.prodMk (Set.Icc.continuous_convexComb_prod.comp
      (continuous_fst.snd.prodMk (continuous_const.prodMk continuous_snd))))
  exact trans_continuous_family _ (symm_continuous_family _ ht) _
    (trans_continuous_family (fun v : ι × I => refl (q v.1 v.2))
      (hq.comp continuous_fst) _ ht)

private theorem continuous_conjLoop_family (hq : Continuous ↿q) (α : Ω (Ω X x) (refl x)) :
    Continuous fun w : (ι × I) × I => (q w.1.1).conjLoop (α w.1.2) w.2 := by
  have hα : Continuous fun w : (ι × I) × I => α w.1.2 w.2 :=
    (continuous_uncurry_iff.2 α.continuous).comp (continuous_fst.snd.prodMk continuous_snd)
  have hq' : Continuous ↿fun v : ι × I => q v.1 :=
    hq.comp (continuous_fst.fst.prodMk continuous_snd)
  exact trans_continuous_family _ (symm_continuous_family _ hq') _
    (trans_continuous_family (fun v : ι × I => α v.2) hα _ hq')

private theorem continuous_conjDoubleLoop_family (hq : Continuous ↿q)
    (α : Ω (Ω X x) (refl x)) :
    Continuous fun w : ι × I × I => (q w.1).conjDoubleLoop α w.2.1 w.2.2 := by
  -- concatenate the families of double loops as families of paths in `C(I, X)`
  have hc : ∀ {a b : X}, Continuous fun ℓ : Path a b => (ℓ : C(I, X)) :=
    continuous_induced_dom
  let P := fun i => ((q i).conjLoopContraction).map hc
  let A := fun i => (α.map (q i).conjLoop.continuous).map hc
  have hP : Continuous ↿P := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_conjLoopContraction_family q hq)
  have hA : Continuous ↿A := ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_conjLoop_family q hq α)
  have hΦ : Continuous ↿fun i => ((q i).conjDoubleLoop α).map hc := by
    have h : (fun i => ((q i).conjDoubleLoop α).map hc) =
        fun i => (P i).symm.trans ((A i).trans (P i)) := by
      funext i
      simp only [conjDoubleLoop, map_trans, map_symm, P, A]
    rw [h]
    exact trans_continuous_family _ (symm_continuous_family _ hP) _
      (trans_continuous_family _ hA _ hP)
  exact continuous_eval.comp
    ((hΦ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd)

end Family

/-- The initial segment of `p` up to time `r`, from `x` to `p r`. -/
private def initSeg (p : Path x y) (r : I) : Path x (p r) :=
  (p.subpath 0 r).cast p.source.symm rfl

/-- The squares of the conjugation transports of `α` along the initial segments of `p`. -/
private def conjDoubleLoopFamily (p : Path x y) (α : Ω (Ω X x) (refl x)) :
    C(I × I^(Fin 2), X) where
  toFun w := (p.initSeg w.1).conjDoubleLoop α (w.2 0) (w.2 1)
  continuous_toFun := by
    have hp : Continuous ↿p.initSeg := p.subpath_continuous_family.comp
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
    have hz : Continuous fun w : I × I^(Fin 2) => (w.1, w.2 0, w.2 1) := by fun_prop
    exact ((continuous_conjDoubleLoop_family p.initSeg hp α).comp hz).congr fun w => rfl

private theorem conjDoubleLoopFamily_apply (p : Path x y) (α : Ω (Ω X x) (refl x)) (r : I)
    (z : I^(Fin 2)) :
    p.conjDoubleLoopFamily α (r, z) = (p.initSeg r).conjDoubleLoop α (z 0) (z 1) :=
  (rfl)

/-- The squares of the conjugation transports along the initial segments of `p` form a homotopy
of generalized loops along `p`. -/
private def conjDoubleLoopHomotopyAlong (p : Path x y) (α : Ω (Ω X x) (refl x)) :
    TauCeti.GenLoop.HomotopyAlong p (GenLoop.fromDoubleLoop ((refl x).conjDoubleLoop α))
      (GenLoop.fromDoubleLoop (p.conjDoubleLoop α)) where
  toContinuousMap := p.conjDoubleLoopFamily α
  map_zero_left z :=
    (conjDoubleLoop_congr (p.initSeg 0) (refl x) (fun u => by simp [initSeg]) α (z 0)
      (z 1)).trans (GenLoop.fromDoubleLoop_apply _ z).symm
  map_one_left z :=
    (conjDoubleLoop_congr (p.initSeg 1) p (fun u => by simp [initSeg]) α (z 0) (z 1)).trans
      (GenLoop.fromDoubleLoop_apply _ z).symm
  map_boundary r z hz := by
    have h : p.conjDoubleLoopFamily α (r, z) = p r := by
      rw [conjDoubleLoopFamily_apply]
      obtain ⟨i, hi | hi⟩ := hz <;> fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
        simp only [hi, Path.source, Path.target, refl_apply]
    exact h

end Path

namespace HomotopyGroup

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- **Conjugation transport is base-point change of `π₂`**: under the identification
`π₁(Ω X x, refl x) ≃* π₂(X, x)`, conjugating loops of loops by a path `p` is the transport
`TauCeti.homotopyGroupTransport p` of second homotopy groups along `p`. -/
@[simp]
theorem fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport (p : Path x y)
    (a : FundamentalGroup (Ω X x) (Path.refl x)) :
    fundamentalGroupLoopSpaceMulEquiv (p.loopSpaceTransport a) =
      TauCeti.homotopyGroupTransport p (fundamentalGroupLoopSpaceMulEquiv a) := by
  obtain ⟨q⟩ := a
  obtain ⟨α, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  have h₀ : FundamentalGroup.fromPath (.mk α) =
      FundamentalGroup.fromPath (.mk ((Path.refl x).conjDoubleLoop α)) := by
    rw [← Path.loopSpaceTransport_fromPath_mk, Path.loopSpaceTransport_refl, MonoidHom.id_apply]
  -- the case split produces `End.of`, of which `FundamentalGroup.fromPath` is an abbreviation
  rw [show (End.of (Path.Homotopic.Quotient.mk α) : FundamentalGroup (Ω X x) (Path.refl x)) =
      FundamentalGroup.fromPath (.mk α) from rfl, Path.loopSpaceTransport_fromPath_mk, h₀,
    fundamentalGroupLoopSpaceMulEquiv_fromPath_mk, fundamentalGroupLoopSpaceMulEquiv_fromPath_mk,
    TauCeti.homotopyGroupTransport_mk]
  exact Quotient.sound (p.conjDoubleLoopHomotopyAlong α).homotopic_transport

end HomotopyGroup
