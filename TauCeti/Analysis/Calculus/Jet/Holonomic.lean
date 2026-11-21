/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Jet.Higher

/-!
# Holonomic tangents and contact one-forms in jet coordinates

The tangent to a prolonged section at order `r` depends on its jet of order `r + 1`.
`holonomicLift` inserts the base direction in the first slot of each next-order derivative.
The companion `jetContact` is the vertical difference between a tangent and its holonomic
part, i.e. the coordinate family `du_I − Σ_μ u_(I+e_μ) dx^μ`. Its components take values in the
ambient spaces of multilinear maps used for jet coordinates; the lift of a symmetric jet
has symmetric components. The contact formulas below concern tangent vectors at the truncated
jet, equivalently the contact generators before pullback along the truncation.

The lift and the contact defect transform under arbitrary base-dependent nonlinear fibre
coordinate changes. A one-form at the truncated jet annihilates every prolonged section with
the given raised jet exactly when it factors through the contact defect.

The jet and contact conventions follow Ian M. Anderson, *The Variational Bicomplex*, Chapter 1,
§A. The construction uses `jetCoordChange` for the Faà di Bruno transition of jet coordinates.
-/

public section

noncomputable section

open ContinuousLinearMap
open scoped ContDiff Topology

namespace TauCeti

variable {𝕜 E E' F G V : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {r : ℕ}

/-- The graph of the coordinate prolongation of a section through order `r`. -/
def jetProlongation (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (r : ℕ) (s : E → F) (x : E) :
    E × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) :=
  (x, fun i ↦ iteratedFDeriv 𝕜 i s x)

@[simp] theorem jetProlongation_fst (s : E → F) (x : E) :
    (jetProlongation 𝕜 r s x).1 = x := (rfl)

@[simp] theorem jetProlongation_snd (s : E → F) (x : E) (i : Fin (r + 1)) :
    (jetProlongation 𝕜 r s x).2 i = iteratedFDeriv 𝕜 i s x := (rfl)

/-- Truncating the coordinate prolongation of a section gives its lower-order prolongation. -/
@[simp] theorem jetTruncate_jetProlongation {m : ℕ} (hmr : m ≤ r) (s : E → F) (x : E) :
    jetTruncate hmr (jetProlongation 𝕜 r s x).2 = (jetProlongation 𝕜 m s x).2 := by
  funext i
  simp

/-- Lift a base tangent vector to the tangent of the order-`r` prolongation specified by the
order-`r + 1` coordinates `j`. Its `i`-th jet component is contraction of `j (i + 1)`. -/
def holonomicLift (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F) :
    E →L[𝕜] E × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) :=
  (ContinuousLinearMap.id 𝕜 E).prod (ContinuousLinearMap.pi fun i ↦ (j i.succ).curryLeft)

@[simp] theorem holonomicLift_fst (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F) (v : E) :
    (holonomicLift j v).1 = v := (rfl)

@[simp] theorem holonomicLift_snd (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F) (v : E)
    (i : Fin (r + 1)) (w : Fin (i : ℕ) → E) :
    (holonomicLift j v).2 i w = j i.succ (Fin.cons v w) :=
  ContinuousMultilinearMap.curryLeft_apply _ _ _

/-- Prolongation to order `r` consumes `r` derivatives of regularity. -/
theorem _root_.ContDiffAt.jetProlongation {s : E → F} {x : E} {m n : ℕ∞ω}
    (hs : ContDiffAt 𝕜 n s x) (hmn : m + r ≤ n) :
    ContDiffAt 𝕜 m (jetProlongation 𝕜 r s) x := by
  refine contDiffAt_id.prodMk (contDiffAt_pi.mpr fun i ↦ hs.iteratedFDeriv_right ?_)
  exact (add_le_add_right (Nat.cast_le.mpr (Nat.lt_succ_iff.mp i.isLt)) m).trans hmn

/-- The derivative of order-`r` prolongation is the holonomic lift of the next jet. -/
theorem _root_.ContDiffAt.hasFDerivAt_jetProlongation {s : E → F} {x : E} {n : ℕ∞ω}
    (hs : ContDiffAt 𝕜 n s x) (hr : (r : ℕ∞ω) < n) :
    HasFDerivAt (jetProlongation 𝕜 r s) (holonomicLift (jetProlongation 𝕜 (r + 1) s x).2) x := by
  refine (hasFDerivAt_id x).prodMk (hasFDerivAt_pi.mpr fun i ↦ ?_)
  have h := hs.differentiableAt_iteratedFDeriv (lt_of_le_of_lt
    (Nat.cast_le.mpr (Nat.lt_succ_iff.mp i.isLt)) hr)
  convert h.hasFDerivAt using 1
  rw [fderiv_iteratedFDeriv]
  rfl

/-- The contact one-form at a raised jet sends a tangent at the truncated jet to its jet
components minus the holonomic jet components over the same base velocity. -/
def jetContact (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F) :
    (E × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F)) →L[𝕜]
      ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) :=
  snd 𝕜 _ _ - (snd 𝕜 _ _).comp ((holonomicLift j).comp (fst 𝕜 _ _))

/-- The contact defect subtracts the contracted next-order coordinate from each component. -/
theorem jetContact_apply (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F)
    (t : E × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F))
    (i : Fin (r + 1)) (w : Fin (i : ℕ) → E) :
    jetContact j t i w = t.2 i w - j i.succ (Fin.cons t.1 w) := by
  simp [jetContact]

@[simp] theorem jetContact_holonomicLift (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F)
    (v : E) : jetContact j (holonomicLift j v) = 0 := by
  simp [jetContact]

@[simp] theorem jetContact_zero_fst (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F)
    (a : (i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) : jetContact j (0, a) = a := by
  simp [jetContact]

/-- A tangent is the sum of the holonomic lift of its base component and its contact defect. -/
theorem holonomicLift_add_jetContact (j : (i : Fin (r + 2)) → E [×(i : ℕ)]→L[𝕜] F)
    (t : E × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F)) :
    holonomicLift j t.1 + (0, jetContact j t) = t := by
  ext <;> simp [jetContact]

/-- A covector annihilates all prolonged tangents through the raised jet `j` if and only if
it is a linear combination of the contact components (with a unique continuous linear
coefficient map on the ambient vertical coordinate space). -/
theorem JetAt.existsUnique_comp_jetContact_iff {x : E} (j : JetAt 𝕜 F (r + 1) x)
    (α : (E × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F)) →L[𝕜] V) :
    (∃! β : ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) →L[𝕜] V,
      α = β.comp (jetContact j.coordinates)) ↔
      ∀ (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x), JetAt.mk s hs = j →
        α.comp (fderiv 𝕜 (jetProlongation 𝕜 r s) x) = 0 := by
  have hderiv (s : E → F) (hs : ContDiffAt 𝕜 ∞ s x) (hj : JetAt.mk s hs = j) :
      fderiv 𝕜 (jetProlongation 𝕜 r s) x = holonomicLift j.coordinates := by
    have hr : (r : ℕ∞ω) < ∞ := WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top r)
    rw [← hj, (hs.hasFDerivAt_jetProlongation hr).fderiv]
    congr 1
    funext i
    simp
  constructor
  · rintro ⟨β, rfl, _⟩ s hs hj
    ext v
    simp [hderiv s hs hj]
  · intro h
    obtain ⟨s, hs, hj⟩ := j.mk_surjective
    have hα := h s hs hj
    rw [hderiv s hs hj] at hα
    refine ⟨α.comp (inr 𝕜 _ _), ?_, ?_⟩
    · apply ContinuousLinearMap.ext
      intro t
      have ht : α (holonomicLift j.coordinates t.1) = 0 := DFunLike.congr_fun hα t.1
      simpa [ht] using congrArg α (holonomicLift_add_jetContact j.coordinates t).symm
    · intro β hβ
      apply ContinuousLinearMap.ext
      intro a
      simpa using DFunLike.congr_fun hβ.symm (0, a)

/-- The derivative of a nonlinear jet transition sends the holonomic lift to the holonomic lift
of the transformed raised jet. With the base change written as `h : E' → E`, the incoming jet
velocity is the lift of `Dh(v)`, while the outgoing base velocity is `v`. -/
theorem JetAt.fderiv_jetCoordChange_holonomicLift {x : E'} {h : E' → E} {g : E' × F → G}
    (j : JetAt 𝕜 F (r + 1) (h x)) (hh : ContDiffAt 𝕜 (r + 1 : ℕ) h x)
    (hg : ContDiffAt 𝕜 (r + 1 : ℕ) g (x, j.value)) (v : E') :
    fderiv 𝕜 (fun p ↦ (p.1, jetCoordChange r h g p.1 p.2))
      (x, jetTruncate (Nat.le_succ r) j.coordinates)
      (v, (holonomicLift j.coordinates (fderiv 𝕜 h x v)).2) =
      holonomicLift (jetCoordChange (r + 1) h g x j.coordinates) v := by
  induction j using JetAt.ind with | h s hs =>
  have hs' : ContDiffAt 𝕜 (r + 1 : ℕ) s (h x) := hs.of_le (by simp)
  simp only [JetAt.value_mk] at hg
  have hr : (r : ℕ∞ω) < ↑(r + 1) := Nat.cast_lt.mpr (Nat.lt_succ_self r)
  have hr' : (1 : ℕ∞ω) + r ≤ ↑(r + 1) := by
    rw [add_comm, ← Nat.cast_one, ← Nat.cast_add]
  let q := fun y ↦ (y, (jetProlongation 𝕜 r s (h y)).2)
  let T := fun p : E' × ((i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) ↦
    (p.1, jetCoordChange r h g p.1 p.2)
  have hq := (hasFDerivAt_id x).prodMk
    (((hs'.hasFDerivAt_jetProlongation hr).comp x (hh.differentiableAt (by simp)).hasFDerivAt).snd)
  have hT : DifferentiableAt 𝕜 T (q x) :=
    (contDiffAt_fst.prodMk (contDiffAt_jetCoordChange hh (g := g) (by
      convert hg using 2
      exact iteratedFDeriv_zero_apply _) hr'))
      |>.differentiableAt (by simp)
  let t := fun y ↦ g (y, s (h y))
  have ht : ContDiffAt 𝕜 (r + 1 : ℕ) t x := hg.comp x (contDiffAt_id.prodMk (hs'.comp x hh))
  have hcomp : T ∘ q =ᶠ[𝓝 x] jetProlongation 𝕜 r t := by
    have hgraph := (contDiffAt_id.prodMk (hs'.comp x hh)).continuousAt
    filter_upwards [hh.eventually (by simp), hgraph.eventually (hg.eventually (by simp)),
      hh.continuousAt.eventually (hs'.eventually (by simp))] with y hhy hgy hsy
    apply Prod.ext
    · simp [T, q]
    · exact jetCoordChange_iteratedFDeriv (hhy.of_le hr.le) (hsy.of_le hr.le) (hgy.of_le hr.le)
  have hd := (hT.hasFDerivAt.comp x hq).congr_of_eventuallyEq hcomp.symm
  have hd' := DFunLike.congr_fun (hd.fderiv.symm.trans (ht.hasFDerivAt_jetProlongation hr).fderiv) v
  have hj : (JetAt.mk s hs : JetAt 𝕜 F (r + 1) (h x)).coordinates =
      (jetProlongation 𝕜 (r + 1) s (h x)).2 := funext fun i ↦ JetAt.coordinates_mk s hs i
  have hj' : jetCoordChange (r + 1) h g x (jetProlongation 𝕜 (r + 1) s (h x)).2 =
      (jetProlongation 𝕜 (r + 1) t x).2 := jetCoordChange_iteratedFDeriv hh hs' hg
  rw [hj, hj', jetTruncate_jetProlongation]
  exact hd'

/-- Under a nonlinear jet transition the contact defect transforms by the vertical block of
its derivative. The horizontal terms cancel even when `g` depends on the base point. -/
theorem JetAt.jetContact_fderiv_jetCoordChange {x : E'} {h : E' → E} {g : E' × F → G}
    (j : JetAt 𝕜 F (r + 1) (h x)) (hh : ContDiffAt 𝕜 (r + 1 : ℕ) h x)
    (hg : ContDiffAt 𝕜 (r + 1 : ℕ) g (x, j.value)) (v : E')
    (a : (i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) :
    let p := (x, jetTruncate (Nat.le_succ r) j.coordinates)
    let DT := fderiv 𝕜 (fun z ↦ (z.1, jetCoordChange r h g z.1 z.2)) p
    jetContact (jetCoordChange (r + 1) h g x j.coordinates) (DT (v, a)) =
      (DT (0, jetContact j.coordinates (fderiv 𝕜 h x v, a))).2 := by
  dsimp only
  let DT := fderiv 𝕜 (fun z ↦ (z.1, jetCoordChange r h g z.1 z.2))
    (x, jetTruncate (Nat.le_succ r) j.coordinates)
  have hsplit : (v, a) = (v, (holonomicLift j.coordinates (fderiv 𝕜 h x v)).2) +
      (0, jetContact j.coordinates (fderiv 𝕜 h x v, a)) := by
    apply Prod.ext (by simp)
    simpa only [Prod.snd_add] using
      (congrArg Prod.snd (holonomicLift_add_jetContact j.coordinates (fderiv 𝕜 h x v, a))).symm
  have hr' : (1 : ℕ∞ω) + r ≤ ↑(r + 1) := by
    rw [add_comm, ← Nat.cast_one, ← Nat.cast_add]
  have hD : DifferentiableAt 𝕜 _ (x, jetTruncate (Nat.le_succ r) j.coordinates) :=
    (contDiffAt_jetCoordChange hh (g := g) (by
      rw [jetTruncate_zero_apply]
      convert hg using 2
      exact JetAt.coordinates_zero_apply j (0 : Fin 0 → E)) hr')
      |>.differentiableAt (by simp)
  have hfst (b : (i : Fin (r + 1)) → E [×(i : ℕ)]→L[𝕜] F) : (DT (0, b)).1 = 0 := by
    dsimp only [DT]
    rw [(hasFDerivAt_fst.prodMk hD.hasFDerivAt).fderiv]
    rfl
  conv_lhs => rw [hsplit]
  rw [map_add, j.fderiv_jetCoordChange_holonomicLift hh hg, map_add, jetContact_holonomicLift,
    zero_add]
  have heq : DT (0, jetContact j.coordinates (fderiv 𝕜 h x v, a)) = (0, (DT _).2) :=
    Prod.ext (hfst _) rfl
  exact (congrArg _ heq).trans (jetContact_zero_fst _ _)

end TauCeti
