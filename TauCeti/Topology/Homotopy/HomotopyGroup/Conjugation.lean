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

Conjugation also turns a *free* homotopy of loops into a based one. A homotopy `F` through loops,
from a loop `γ₀` at `x` to a loop `γ₁` at `y`, is a `ContinuousMap.HomotopyWith` of maps `I → X`
for the property `g 0 = g 1`; it is a cylinder whose seam, the path `F.basepointPath` traced by
the base points of its loops, runs from `x` to `y`. Conjugating the loop of `F` at time `a` by the
tail of the seam from time `a` gives a path of loops at `y` from
`F.basepointPath.conjLoop γ₀` to `(Path.refl y).conjLoop γ₁`, and the reverse of the
reparametrization `Path.conjLoopReflPath γ₁` ends it at `γ₁`. Its class is the morphism
`F.conjLoopHom` of the fundamental groupoid of `Ω X y`. When the seam stays at `x`, `F` is
already a homotopy of loops at `x`, `F.loopPath`, and `F.conjLoopHom` is its class up to these
identifications (`ContinuousMap.HomotopyWith.conjLoopHom_eq_eqToHom_comp`).

## Main definitions

* `Path.conjLoop p : C(Ω X x, Ω X y)`: conjugation of loops by `p`.
* `Path.conjLoopContraction p`: the contraction of `p⁻¹ ⬝ refl ⬝ p` to the constant loop at `y`.
* `Path.loopSpaceTransport p`: the conjugation transport on fundamental groups of loop spaces.
* `Path.conjLoopReflPath ℓ`: the reparametrization of a loop `ℓ` into its conjugate by the
  constant path.
* `ContinuousMap.HomotopyWith.basepointPath F`, `ContinuousMap.HomotopyWith.conjLoopHom F`: the
  seam of a free homotopy of loops `F`, and the class of the based homotopy of loops obtained by
  conjugating `F` along its seam.

## Main results

* `Path.map_comp_conjLoopContraction`: conjugation intertwines the action of loops of loops
  with conjugation transport, in the fundamental groupoid of `Ω X y`.
* `Path.loopSpaceTransport_refl`: conjugation by a constant path acts trivially.
* `HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport`: conjugation transport is
  base-point change of `π₂` along `p`.
* `Path.mk_conjLoopReflPath_comp_map`: the reparametrization by the constant path is natural.
* `ContinuousMap.HomotopyWith.conjLoopHom_eq_eqToHom_comp`: for a free homotopy of loops whose
  seam is constant, the conjugated homotopy is the homotopy of loops itself.

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
  continuous_toFun := Path.continuous_trans.comp
    (continuous_const.prodMk (Path.continuous_trans.comp (continuous_id.prodMk continuous_const)))

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
def conjLoopContraction (p : Path x y) : Path (p.conjLoop (Path.refl x)) (Path.refl y) where
  toFun a := (p.tail a).symm.trans ((Path.refl (p a)).trans (p.tail a))
  continuous_toFun := by
    have ht : Continuous ↿p.tail := p.subpath_continuous_family.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    exact Path.continuous_uncurry_iff.1 <| Path.trans_continuous_family _
      (Path.symm_continuous_family _ ht) _
      (Path.trans_continuous_family _ (p.continuous.comp continuous_fst) _ ht)
  source' := by
    ext t
    simp [tail, Path.trans_apply]
  target' := by
    ext t
    simp [tail_apply, Path.trans_apply]

theorem conjLoopContraction_apply (p : Path x y) (a : I) :
    p.conjLoopContraction a =
      ((p.subpath a 1).cast rfl p.target.symm).symm.trans
        ((Path.refl (p a)).trans ((p.subpath a 1).cast rfl p.target.symm)) :=
  (rfl)

/-- **Conjugation transport** on fundamental groups of loop spaces along a path `p` from `x` to
`y`: the map induced by conjugation of loops by `p`, followed by base-point change along the
contraction `Path.conjLoopContraction p`. It is base-point change of `π₂` along `p`
(`HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_loopSpaceTransport`). -/
def loopSpaceTransport (p : Path x y) :
    FundamentalGroup (Ω X x) (Path.refl x) →* FundamentalGroup (Ω X y) (Path.refl y) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath p.conjLoopContraction).toMonoidHom.comp
    (FundamentalGroup.map p.conjLoop (Path.refl x))

theorem loopSpaceTransport_apply (p : Path x y) (a : FundamentalGroup (Ω X x) (Path.refl x)) :
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
    (a : FundamentalGroup (Ω X x) (Path.refl x)) :
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
  (Path.refl 0).symm.trans ((⟨ContinuousMap.id I, rfl, rfl⟩ : Path (0 : I) 1).trans (Path.refl 1))

private theorem conjLoop_refl (ℓ : Ω X x) :
    (Path.refl x).conjLoop ℓ =
      ℓ.reparam conjReparam conjReparam.continuous conjReparam.source conjReparam.target := by
  ext t
  rw [Path.coe_reparam, Function.comp_apply, conjLoop_apply, conjReparam]
  simp only [Path.trans_apply, Path.refl_symm, Path.refl_apply]
  split_ifs
  exacts [ℓ.source.symm, rfl, ℓ.target.symm]

/-- The homotopy from the identity of `Ω X x` to conjugation by the constant path, which
reparametrizes every loop in the same way (`Path.reparamHomotopy`). It fixes the constant
loop. -/
private def conjLoopReflHomotopy (x : X) :
    (ContinuousMap.id (Ω X x)).Homotopy (Path.refl x).conjLoop :=
  (Path.reparamHomotopy conjReparam conjReparam.continuous conjReparam.source
    conjReparam.target).cast rfl (ContinuousMap.ext fun ℓ => (conjLoop_refl ℓ).symm)

private theorem conjLoopContraction_refl_apply (a : I) :
    (Path.refl x).conjLoopContraction a = Path.refl x := by
  ext t
  simp [conjLoopContraction_apply, Path.trans_apply, Path.subpath]

private theorem evalAt_conjLoopReflHomotopy (x : X) :
    (conjLoopReflHomotopy x).evalAt (Path.refl x) = (Path.refl x).conjLoopContraction.symm := by
  -- every point of both paths is the constant loop
  refine Path.ext (funext fun u => ?_)
  have h : (conjLoopReflHomotopy x).evalAt (Path.refl x) u = Path.refl x := by
    rw [ContinuousMap.Homotopy.evalAt_apply]
    ext t
    -- `Path.Homotopy.reparam` evaluates the constant loop, so it is constant by definition
    exact (congrArg (fun ℓ : Ω X x => ℓ t) (Path.reparamHomotopy_apply _ _ _ _ u _)).trans rfl
  exact h.trans (conjLoopContraction_refl_apply (σ u)).symm

/-- The path in `Ω X x` from a loop `ℓ` to its conjugate `(Path.refl x).conjLoop ℓ` by the
constant path, which reparametrizes `ℓ`. It is the trace at `ℓ` of a homotopy from the identity
of `Ω X x` to conjugation by the constant path. -/
def conjLoopReflPath (ℓ : Ω X x) : Path ℓ ((Path.refl x).conjLoop ℓ) :=
  (conjLoopReflHomotopy x).evalAt ℓ

/-- **Naturality of the reparametrization**: in the fundamental groupoid of `Ω X x`, following
`Path.conjLoopReflPath ℓ` and then the image of a path class `D` under conjugation by the constant
path is `D` followed by `Path.conjLoopReflPath ℓ'`. -/
@[reassoc]
theorem mk_conjLoopReflPath_comp_map {ℓ ℓ' : Ω X x}
    (D : (⟨ℓ⟩ : FundamentalGroupoid (Ω X x)) ⟶ ⟨ℓ'⟩) :
    FundamentalGroupoid.fromPath (Homotopic.Quotient.mk (conjLoopReflPath ℓ)) ≫
        (FundamentalGroupoid.map (Path.refl x).conjLoop).map D =
      D ≫ FundamentalGroupoid.fromPath (Homotopic.Quotient.mk (conjLoopReflPath ℓ')) := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso (conjLoopReflHomotopy x)).naturality D
  simp only [FundamentalGroupoidFunctor.homotopicMapsNatIso_app] at h
  -- `h` states the same with `D` replaced by its image under the identity, which is `D` once a
  -- representative is chosen
  induction D using Homotopic.Quotient.ind with
  | mk D => exact h.symm

/-- Reparametrizing the constant loop into its conjugate by the constant path and then following
the contraction `Path.conjLoopContraction` of the conjugated constant loop is trivial. -/
@[reassoc (attr := simp)]
theorem mk_conjLoopReflPath_comp_mk_conjLoopContraction (x : X) :
    FundamentalGroupoid.fromPath (Homotopic.Quotient.mk (conjLoopReflPath (Path.refl x))) ≫
        FundamentalGroupoid.fromPath (Homotopic.Quotient.mk (Path.refl x).conjLoopContraction) =
      𝟙 (⟨Path.refl x⟩ : FundamentalGroupoid (Ω X x)) := by
  rw [conjLoopReflPath, evalAt_conjLoopReflHomotopy]
  exact Homotopic.Quotient.symm_trans (Homotopic.Quotient.mk _)

/-- The double loop `c⁻¹ ⬝ (conj_p α ⬝ c)` representing the conjugation transport of the class
of `α`, where `c` is the contraction `Path.conjLoopContraction p`. -/
private def conjDoubleLoop (p : Path x y) (α : Ω (Ω X x) (Path.refl x)) :
    Ω (Ω X y) (Path.refl y) :=
  p.conjLoopContraction.symm.trans ((α.map p.conjLoop.continuous).trans p.conjLoopContraction)

private theorem loopSpaceTransport_fromPath_mk (p : Path x y) (α : Ω (Ω X x) (Path.refl x)) :
    p.loopSpaceTransport (FundamentalGroup.fromPath (.mk α)) =
      FundamentalGroup.fromPath (.mk (p.conjDoubleLoop α)) := by
  simp [loopSpaceTransport, conjDoubleLoop, FundamentalGroup.fundamentalGroupMulEquivOfPath_apply,
    Path.Homotopic.Quotient.mk_map]

/-- **Conjugation by a constant path acts trivially** on the fundamental group of the loop
space. -/
@[simp]
theorem loopSpaceTransport_refl (x : X) :
    (Path.refl x).loopSpaceTransport = MonoidHom.id _ := by
  refine MonoidHom.ext fun g => ?_
  have hid : FundamentalGroup.map (ContinuousMap.id (Ω X x)) (Path.refl x) g = g :=
    DFunLike.congr_fun (FundamentalGroup.map_id _) g
  -- freely homotopic maps agree on `π₁` up to base-point change along the trace
  have h : (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (Path.refl x).conjLoopContraction).symm g =
        FundamentalGroup.map (Path.refl x).conjLoop (Path.refl x) g := by
    have h := (conjLoopReflHomotopy x).fundamentalGroupMulEquivOfPath_evalAt_map (Path.refl x) g
    rw [hid, evalAt_conjLoopReflHomotopy] at h
    rwa [← FundamentalGroup.fundamentalGroupMulEquivOfPath_symm]
  rw [loopSpaceTransport, MonoidHom.comp_apply, ← h, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.id_apply]

/-! ### Conjugation along a continuous family of paths -/

/-- The double loops `conjDoubleLoop q α` depend only on the values of `q`. -/
private theorem conjDoubleLoop_congr {b b' : X} (q : Path x b) (q' : Path x b')
    (h : ∀ u, q u = q' u) (α : Ω (Ω X x) (Path.refl x)) (s t : I) :
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
  exact Path.trans_continuous_family _ (Path.symm_continuous_family _ ht) _
    (Path.trans_continuous_family (fun v : ι × I => Path.refl (q v.1 v.2))
      (hq.comp continuous_fst) _ ht)

private theorem continuous_conjLoop_family (hq : Continuous ↿q) (α : Ω (Ω X x) (Path.refl x)) :
    Continuous fun w : (ι × I) × I => (q w.1.1).conjLoop (α w.1.2) w.2 := by
  have hα : Continuous fun w : (ι × I) × I => α w.1.2 w.2 :=
    (Path.continuous_uncurry_iff.2 α.continuous).comp (continuous_fst.snd.prodMk continuous_snd)
  have hq' : Continuous ↿fun v : ι × I => q v.1 :=
    hq.comp (continuous_fst.fst.prodMk continuous_snd)
  exact Path.trans_continuous_family _ (Path.symm_continuous_family _ hq') _
    (Path.trans_continuous_family (fun v : ι × I => α v.2) hα _ hq')

private theorem continuous_conjDoubleLoop_family (hq : Continuous ↿q)
    (α : Ω (Ω X x) (Path.refl x)) :
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
      simp only [conjDoubleLoop, Path.map_trans, Path.map_symm, P, A]
    rw [h]
    exact Path.trans_continuous_family _ (Path.symm_continuous_family _ hP) _
      (Path.trans_continuous_family _ hA _ hP)
  exact continuous_eval.comp
    ((hΦ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk continuous_snd.snd)

end Family

/-- The initial segment of `p` up to time `r`, from `x` to `p r`. -/
private def initSeg (p : Path x y) (r : I) : Path x (p r) :=
  (p.subpath 0 r).cast p.source.symm rfl

/-- The squares of the conjugation transports of `α` along the initial segments of `p`. -/
private def conjDoubleLoopFamily (p : Path x y) (α : Ω (Ω X x) (Path.refl x)) :
    C(I × I^(Fin 2), X) where
  toFun w := (p.initSeg w.1).conjDoubleLoop α (w.2 0) (w.2 1)
  continuous_toFun := by
    have hp : Continuous ↿p.initSeg := p.subpath_continuous_family.comp
      (continuous_const.prodMk (continuous_fst.prodMk continuous_snd))
    have hz : Continuous fun w : I × I^(Fin 2) => (w.1, w.2 0, w.2 1) := by fun_prop
    exact ((continuous_conjDoubleLoop_family p.initSeg hp α).comp hz).congr fun w => rfl

private theorem conjDoubleLoopFamily_apply (p : Path x y) (α : Ω (Ω X x) (Path.refl x)) (r : I)
    (z : I^(Fin 2)) :
    p.conjDoubleLoopFamily α (r, z) = (p.initSeg r).conjDoubleLoop α (z 0) (z 1) :=
  (rfl)

/-- The squares of the conjugation transports along the initial segments of `p` form a homotopy
of generalized loops along `p`. -/
private def conjDoubleLoopHomotopyAlong (p : Path x y) (α : Ω (Ω X x) (Path.refl x)) :
    TauCeti.GenLoop.HomotopyAlong p (GenLoop.fromDoubleLoop ((Path.refl x).conjDoubleLoop α))
      (GenLoop.fromDoubleLoop (p.conjDoubleLoop α)) where
  toContinuousMap := p.conjDoubleLoopFamily α
  map_zero_left z :=
    (conjDoubleLoop_congr (p.initSeg 0) (Path.refl x) (fun u => by simp [initSeg]) α (z 0)
      (z 1)).trans (GenLoop.fromDoubleLoop_apply _ z).symm
  map_one_left z :=
    (conjDoubleLoop_congr (p.initSeg 1) p (fun u => by simp [initSeg]) α (z 0) (z 1)).trans
      (GenLoop.fromDoubleLoop_apply _ z).symm
  map_boundary r z hz := by
    have h : p.conjDoubleLoopFamily α (r, z) = p r := by
      rw [conjDoubleLoopFamily_apply]
      obtain ⟨i, hi | hi⟩ := hz <;> fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one] at hi <;>
        simp only [hi, Path.source, Path.target, Path.refl_apply]
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

/-! ### Free homotopies of loops

A homotopy `F` of loops whose base point moves, from a loop `γ₀` at `x` to a loop `γ₁` at `y`, is a
homotopy of maps `I → X` through loops (`ContinuousMap.HomotopyWith` for the property
`g 0 = g 1`). Its base points trace the path `F.basepointPath` from `x` to `y`. Conjugating each
intermediate loop by the tail of this path from its base point gives a path of loops at `y`, from
`F.basepointPath.conjLoop γ₀` to `γ₁` up to the reparametrization `Path.conjLoopReflPath`;
its class is `F.conjLoopHom`. -/

namespace ContinuousMap.HomotopyWith

variable {X : Type*} [TopologicalSpace X] {x y : X} {γ₀ : Ω X x} {γ₁ : Ω X y}
  (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1)

/-- The **base-point path** of a free homotopy of loops: the path `s ↦ F (s, 0)` traced by the
base points of its loops, from the base point `x` of `γ₀` to the base point `y` of `γ₁`. -/
def basepointPath : Path x y where
  toFun s := F (s, 0)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
theorem basepointPath_apply (s : I) : F.basepointPath s = F (s, 0) :=
  (rfl)

/-- The loop `t ↦ F (s, t)` of a free homotopy of loops at time `s`, based at `F (s, 0)`. -/
def loopAt (s : I) : Ω X (F.basepointPath s) where
  toFun t := F (s, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := (F.prop s).symm

@[simp]
theorem loopAt_apply (s t : I) : F.loopAt s t = F (s, t) :=
  (rfl)

/-- The path of loops at `y` obtained from a free homotopy of loops by conjugating its loop at
time `a` by the tail of the base-point path from time `a`. -/
private def conjLoopPath : Path (F.basepointPath.conjLoop γ₀) ((Path.refl y).conjLoop γ₁) where
  toFun a := (F.basepointPath.tail a).symm.trans ((F.loopAt a).trans (F.basepointPath.tail a))
  continuous_toFun := by
    have ht : Continuous ↿F.basepointPath.tail := F.basepointPath.subpath_continuous_family.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
    have hl : Continuous ↿F.loopAt := F.continuous
    exact Path.continuous_uncurry_iff.1 <| Path.trans_continuous_family _
      (Path.symm_continuous_family _ ht) _ (Path.trans_continuous_family _ hl _ ht)
  source' := by
    ext t
    simp [Path.tail, Path.trans_apply]
  target' := by
    ext t
    simp [Path.tail_apply, Path.trans_apply]

/-- The **based homotopy class of a free homotopy of loops**: the class, in the fundamental
groupoid of the loop space `Ω X y`, of the path of loops from `F.basepointPath.conjLoop γ₀` to
`γ₁` that conjugates every loop of `F` by the tail of its base-point path. -/
def conjLoopHom :
    (⟨F.basepointPath.conjLoop γ₀⟩ : FundamentalGroupoid (Ω X y)) ⟶ ⟨γ₁⟩ :=
  FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk F.conjLoopPath) ≫
    inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.conjLoopReflPath γ₁)))

section Based

variable {γ₀ γ₁ : Ω X x} (F : HomotopyWith (γ₀ : C(I, X)) γ₁ fun g => g 0 = g 1)

/-- The homotopy of loops at `x` given by a free homotopy of loops whose base point stays at
`x`: the path `s ↦ F (s, ·)` in `Ω X x`. -/
def loopPath (h : ∀ s, F (s, 0) = x) : Path γ₀ γ₁ where
  toFun s := (F.loopAt s).cast (h s).symm (h s).symm
  continuous_toFun := Path.continuous_uncurry_iff.1 F.continuous
  source' := Path.ext (funext fun t => F.apply_zero t)
  target' := Path.ext (funext fun t => F.apply_one t)

@[simp]
theorem loopPath_apply (h : ∀ s, F (s, 0) = x) (s t : I) : F.loopPath h s t = F (s, t) :=
  (rfl)

/-- If the base point of every loop of `F` is `x`, the base-point path of `F` is constant. -/
theorem basepointPath_eq_refl (h : ∀ s, F (s, 0) = x) : F.basepointPath = Path.refl x :=
  Path.ext (funext fun s => (F.basepointPath_apply s).trans (h s))

/-- **A free homotopy of loops with a fixed base point** is, after conjugation, its own homotopy
of loops: if the base point of every loop of `F` is `x`, then `F.conjLoopHom` is the homotopy
class of `F.loopPath`, preceded by the identification of `F.basepointPath.conjLoop γ₀` with
`(Path.refl x).conjLoop γ₀` and the reparametrization `Path.conjLoopReflPath γ₀` backwards. -/
theorem conjLoopHom_eq_eqToHom_comp (h : ∀ s, F (s, 0) = x) :
    F.conjLoopHom = eqToHom (congrArg (fun q : Path x x =>
        (⟨q.conjLoop γ₀⟩ : FundamentalGroupoid (Ω X x))) (F.basepointPath_eq_refl h)) ≫
      inv (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (Path.conjLoopReflPath γ₀))) ≫
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk (F.loopPath h)) := by
  have hb : F.basepointPath.conjLoop γ₀ = (Path.refl x).conjLoop γ₀ :=
    congrArg (fun q : Path x x => q.conjLoop γ₀) (F.basepointPath_eq_refl h)
  set Q := (F.loopPath h).map (Path.refl x).conjLoop.continuous
  -- conjugating by the tails of a constant base-point path is conjugating by the constant path
  have hA : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk F.conjLoopPath) =
      eqToHom (congrArg FundamentalGroupoid.mk hb) ≫
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk Q) := by
    have hc := FundamentalGroupoid.conj_eqToHom (p := Path.Homotopic.Quotient.mk Q) hb rfl
    rw [eqToHom_refl, Category.comp_id] at hc
    rw [hc, ← Path.Homotopic.Quotient.mk_cast]
    refine congrArg (fun q => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk q))
      (Path.ext (funext fun a => Path.ext (funext fun t => ?_)))
    simp [conjLoopPath, Q, Path.tail_apply, Path.trans_apply, h]
  have hR := Path.mk_conjLoopReflPath_comp_map (Path.Homotopic.Quotient.mk (F.loopPath h))
  rw [FundamentalGroupoid.map_map, ← Path.Homotopic.Quotient.mk_map] at hR
  rw [conjLoopHom, hA, Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  exact hR

end Based

end ContinuousMap.HomotopyWith
